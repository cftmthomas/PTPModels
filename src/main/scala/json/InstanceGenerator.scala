package json

import modelling._
import utils.{Time, TimeWindow}

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer
import scala.util.Random

/**
  * Random instance generator. Note: coordinates are generated on a euclidean plane in a circle centered in (0, 0).
  * @param H Number of hospitals
  * @param V Number of vehicles
  * @param P Number of Patients
  * @param seed: (optional) random seed of the instance
  */
class InstanceGenerator(
                         val H: Int, //Number of hospitals
                         val V: Int, //Number of vehicles
                         val P: Int, //Number of patients
                         val seed: Int = math.abs(Random.nextInt())
                       ){
  /**
    * parameters
    */

  var version: Double  = 0.4

  var pCategories = Array(0) //Patient types

  //Min and max time of rdv (h):
  var tMin: Int = 8
  var tMax: Int = 16

  //Min and max loads of patients:
  var minLoad: Int = 1
  var maxLoad: Int = 2

  //Chance of single trip:
  var singleTripProba: Double = 0.2

  //Chance of different start and end for patients (only if double trip):
  var diffPlacesProba: Double = 0.1

  //Chance of mandatory patient:
  var mandatoryProba: Double = 0.3

  //Min and max duration of appointments (min):
  var minDuration: Int = 15
  var maxDuration: Int = math.min((tMax-tMin)*60, 180)

  //Min and max service time of patients (min):
  var minService: Int = 1
  var maxService: Int = 2

  var maxWaitTime: Int = 30 //Max waiting time for patients (min)
  var radius: Int = (maxWaitTime - maxService*2)/2 //Max radius for coordinates

  //Min and max capacity of vehicles:
  var minCapa: Int = 4
  var maxCapa: Int = 6

  //Min and max availability of vehicles (h):
  var minAvailability: Int = (endTime-startTime)
  var maxAvailability: Int = endTime-startTime

  var sameDepot = true //Enforces that all vehicles start at the same place (enforced if sameVehicles)
  var sameVehicles = true //Enforces that all vehicles have the same profile
  var sameVehicleBackward = false //Enforces that the same vehicle brings back the patient

  //actual start and end time (h):
  def startTime: Int = (tMin*60 - radius*2 - maxService)/60
  def endTime: Int = (tMax*60 + radius*2 + maxDuration + maxService)/60+1


  Random.setSeed(seed)
  private var id = 0

  def getId: Int = {
    val newId = id
    id +=1
    newId
  }

  def probaTrue(proba: Double): Boolean = proba == 1 || Random.nextDouble() < proba

  def getRandomInInterval(min: Int, max: Int): Int = Random.nextInt(max+1 - min) + min

  def generateCoordinates(): (Double, Double) = {
    val u = Random.nextDouble()
    val v = Random.nextDouble()

    val w = radius * math.sqrt(u)
    val t = 2 * math.Pi * v
    val x = w * math.cos(t)
    val y = w * math.sin(t)

    (x, y)
  }

  def euclideanDist(x1: Double, y1: Double, x2: Double, y2: Double): Double =
    math.sqrt(math.pow(x2-x1, 2) + math.pow(y2-y1, 2))

  def computeAvailability(): Array[String] = {
    val unavailableTime = (endTime-startTime) - getRandomInInterval(minAvailability, maxAvailability)
    if(unavailableTime == 0) Array(TimeWindow(Time(startTime, 0), Time(endTime, 0)).toString())
    else{
      val unavailableStart = getRandomInInterval(startTime, endTime-unavailableTime)
      val interval1 = TimeWindow(Time(startTime, 0), Time(unavailableStart, 0))
      val interval2 = TimeWindow(Time(unavailableStart + unavailableTime, 0), Time(endTime, 0))
      if(interval1.duration == 0) Array(interval2.toString())
      else if(interval2.duration == 0) Array(interval1.toString())
      else Array(interval1.toString(), interval2.toString())
    }
  }

  def generateVehicles(depots: Array[Place]): Array[Vehicle] = {
    if(sameVehicles){
      val canTake = pCategories
      val capacity = getRandomInInterval(minCapa, maxCapa)
      val availability = computeAvailability()
      Array.fill[Vehicle](V)(Vehicle(getId, canTake, depots.head.id, depots.head.id, capacity, availability))
    }
    else{
      //distributing patient types:
      val canTake = Array.fill[mutable.Set[Int]](V)(mutable.Set())
      for(category <- pCategories) canTake(Random.nextInt(V)) += category
      for(i <- canTake.indices){
        if(canTake(i).isEmpty) canTake(i) += pCategories (Random.nextInt(pCategories.length))
      }

      //Generating vehicles:
      Array.tabulate[Vehicle](V)(i => {
        val depot = depots.lift(i).getOrElse(depots.head)
        Vehicle(
          getId,
          canTake(i).toArray.sorted,
          depot.id,
          depot.id,
          getRandomInInterval(minCapa, maxCapa),
          computeAvailability()
        )
      })
    }
  }

  def generatePlace(category: Int): Place = {
    val coordinates = generateCoordinates()
    Place(getId, coordinates._1, coordinates._2, category)
  }

  def generatePatient(start: Int, dest: Int, end: Int): Patient = {
    val category = pCategories(Random.nextInt(pCategories.length))
    val load = getRandomInInterval(minLoad, maxLoad)
    val rdvTime = Time.intToTime(getRandomInInterval(tMin*60, tMax*60)).toString()
    val rdvDur = Time.intToTime(getRandomInInterval(minDuration, maxDuration)).toString()
    val srvDur = Time.intToTime(getRandomInInterval(minService, maxService)).toString()
    val mandatory = probaTrue(mandatoryProba)
    Patient(getId, category, load, start, dest, end, rdvTime, rdvDur, srvDur, Some(mandatory))
  }

  /**
    * generates a random instance
    */
  def generateInstance(name: String = "PTP-RAND_" + H + "_" + V + "_" + P): PTPInstance ={

    val hospitals: Array[Place] = Array.fill[Place](H){generatePlace(0)}

    val depots: Array[Place] =
      if(sameVehicles || sameDepot) Array(generatePlace(1))
      else Array.fill[Place](V){generatePlace(1)}

    //Generating patient places:
    val patientPlaces = ArrayBuffer[Place]()
    val travelStops = Array.tabulate[(Int, Int, Int)](P){i =>
      //Selecting hospital:
      val h = if(i < hospitals.length) i //At least one patient is attributed to each hospital
      else hospitals(Random.nextInt(hospitals.length)).id

      //Generating patient place:
      val p = generatePlace(2)
      patientPlaces += p

      if(probaTrue(singleTripProba)){
        if(Random.nextBoolean()) (p.id, h, -1)
        else (-1, h, p.id)
      }
      else if(probaTrue(diffPlacesProba)){
        val p2 = generatePlace(2)
        patientPlaces += p2
        (p.id, h, p2.id)
      }
      else (p.id, h, p.id)
    }

    val places = hospitals ++ depots ++ patientPlaces

    val vehicles: Array[Vehicle] = generateVehicles(depots)

    val patients = travelStops.map{case (start, dest, end) => generatePatient(start, dest, end)}

    val distMatrix = Array.tabulate(places.length, places.length)((i, j) =>
      math.round(euclideanDist(places(i).lat, places(i).long, places(j).lat, places(j).long)).toInt
    )

    PTPInstance(version.toString, seed, name, "Eucl", sameVehicleBackward, Time(maxWaitTime).toString(), places, vehicles, patients, distMatrix)
  }

  def generate(filepath: String, name: String = "PTP-RAND_" + H + "_" + V + "_" + P): Unit = {
    val instance = generateInstance(name)
    JsonParser.writeInstance(filepath, instance)
  }
}
