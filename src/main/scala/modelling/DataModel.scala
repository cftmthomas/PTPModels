package modelling

import utils.Time

import scala.collection.mutable

case class Place(
                  id: Int,
                  lat: Double,
                  long: Double,
                  category: Int, //0: hospital, 1: Depot, 2: Patient
                )

case class Vehicle(
                    id: Int,
                    canTake: Array[Int], //Array of patient categories that the vehicle can take
                    start: Int, //Id of start depot (negative represents null val)
                    end: Int, //Id of end depot (negative represents null val)
                    capacity: Int,
                    availability: Array[String] //Set of time windows when the vehicle is available
                  )

case class Patient(
                    id: Int,
                    category: Int,
                    load: Int,
                    start: Int, //Id of start place (negative represents null val)
                    destination: Int, //Id of destination
                    end: Int, //Id of en place (negative represents null val)
                    rdvTime: String,
                    rdvDuration: String,
                    srvDuration: String,  //Time needed at stops to embark/disembark
                    mandatory: Option[Boolean]
                  ) {
  def rdvStart: Int = Time(rdvTime).toInt

  def rdvLen: Int = Time(rdvDuration).toInt

  def rdvEnd: Int = rdvStart + rdvLen

  def srvLen: Int = Time(srvDuration).toInt

  def isMandatory: Boolean = mandatory.getOrElse(false)
}

/**
  * Represents a PTP instance.
  */
case class PTPInstance(
                        version: String,
                        id: Int,
                        name: String,
                        coordType: String, //Type of coordinates: "Geo": geographical coordinates, "Eucl": euclidean points
                        sameVehicleBackward: Boolean, //Enforces that the same vehicle makes the two trips for a patient
                        maxWaitTime: String, //Maximum waiting time for patients
                        places: Array[Place], //Ids must be unique consecutive ints starting at 0 for places vehicles and patients in this order.
                        vehicles: Array[Vehicle],
                        patients: Array[Patient],
                        distMatrix: Array[Array[Int]] //Distance matrix between all places
                      ) {
  def nPlaces: Int = places.length

  def nVehicles: Int = vehicles.length

  def nPatients: Int = patients.length

  def getPlaceById(i: Int): Place = {
    if(i >= 0 && i < places.length && places(i).id == i) places(i)
    else{
      for(p <- places){
        if(p.id == i) return p
      }
      throw new Exception("Invalid id: unable to find place " + i)
    }
  }

  def getVehicleById(i: Int): Vehicle = {
    if(i - nPlaces >= 0 && i - nPlaces < vehicles.length && vehicles(i - nPlaces).id == i) vehicles(i - nPlaces)
    else{
      for(v <- vehicles){
        if(v.id == i) return v
      }
      throw new Exception("Invalid id: unable to find vehicle " + i)
    }
  }

  def getPatientById(i: Int): Patient = {
    if(i - nPlaces - nVehicles >= 0 && i - nPlaces - nVehicles < patients.length && patients(i - nPlaces - nVehicles).id == i) patients(i - nPlaces - nVehicles)
    else{
      for(p <- patients){
        if(p.id == i) return p
      }
      throw new Exception("Invalid id: unable to find patient " + i)
    }
  }

  def minTravelTime(p: Int, forward: Boolean): Int = {
    val patient = getPatientById(p)
    val origin = if(forward && patient.start >= 0) patient.start else patient.destination
    val dest = if(forward || patient.end < 0) patient.destination else patient.end
    distMatrix(origin)(dest) + patient.srvLen * 2
  }

  def isValid(verbose: Boolean = true): Boolean = {
    val ids = mutable.Set[Int]()

    for(i <- places.indices){
      val id = places(i).id

      if(id != i){
        if(verbose) println("Place id " + id + " is not consistent with index position " + i)
        return false
      }

      if(ids.contains(id)){
        if(verbose) println("Id " + id + " is not unique")
        return false
      }

      ids += id
    }

    for(v <- vehicles){
      val id = v.id

      if(ids.contains(id)){
        if(verbose) println("Id " + id + " is not unique")
        return false
      }

      ids += id
    }

    for(p <- patients){
      val id = p.id

      if(ids.contains(id)){
        if(verbose) println("Id " + id + " is not unique")
        return false
      }

      ids += id
    }

    true
  }
}

/**
  * Represents a part of a solution path.
  * @param place Place id.
  * @param time Arrival time at place.
  * @param patient Patient serviced id.
  * @param operation 0: load forward, 1: unload forward, 2: load backward, 3: unload backward.
  */
case class Step(
                 place: Int,
                 time: String,
                 patient: Int,
                 operation: Int,
               )

/**
  * Represents the itinerary of one vehicle as part of a solution.
  * @param vehicle The vehicle.
  * @param steps The set of steps.
  */
case class Path(vehicle: Int, steps: Array[Step]) //Path for one vehicle

/**
  * Represents a solution to a PTP instance.
  * @param instance the instance.
  * @param paths the path for each vehicle (set of steps)
  */
case class Solution(instance: PTPInstance, paths: Array[Path]){

  /**
    * Computes the number of patients serviced
    * @return
    */
  def nPatientsServiced: Int = paths.flatMap(_.steps.map(_.patient)).distinct.length

  /**
    * Computes the total waiting time of the patients (difference between rdv <-> start/return and min transport time)
    * @return total waiting time
    */
  def totalWaitingTime: Int = {
    val pickDropTime = mutable.Map[Int, (Int, Int)]()
    for(path <- paths){
      for(step <- path.steps){
        if(step.operation == 0 && step.place == instance.getPatientById(step.patient).start){
          val mapEntry = pickDropTime.getOrElse(step.patient, (-1, -1))
          pickDropTime(step.patient) = (Time(step.time).toMinutes, mapEntry._2)
        }
        else if(step.operation == 1 && step.place == instance.getPatientById(step.patient).end){
          val mapEntry = pickDropTime.getOrElse(step.patient, (-1, -1))
          pickDropTime(step.patient) = (mapEntry._1, Time(step.time).toMinutes)
        }
      }
    }

    pickDropTime.map{case (p, (pick, drop)) => {
      val patient = instance.getPatientById(p)
      val forwardWait = if(pick >= 0) (patient.rdvStart - pick) - instance.minTravelTime(p, forward = true) else 0
      val backwardWait = if(drop >= 0) (drop + patient.srvLen - patient.rdvEnd) - instance.minTravelTime(p, forward = false) else 0
      forwardWait + backwardWait
    }}.sum
  }
}
