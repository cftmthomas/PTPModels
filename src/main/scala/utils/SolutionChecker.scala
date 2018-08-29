package utils

import json.JsonParser
import modelling.Solution

object SolutionChecker extends App{

  val path = args(0)
  val sol = JsonParser.readSol(path)
  println(checkSol(sol))

  def checkSol(sol: Solution, verbose: Boolean = true, softMandatoryCst: Boolean = true): Boolean = {
    val ist = sol.instance
    val satisfied = ist.patients.map(p => (p.id, Array.fill[Int](4)(-1))).toMap

    for(path <- sol.paths){
      val v = sol.instance.getVehicleById(path.vehicle)
      val steps = path.steps
      val windows = v.availability.map(TimeWindow(_))
      var currLoad = 0
      var currTime = 0
      for((s, j) <- steps.zipWithIndex){
        val p = ist.getPatientById(s.patient)
        val t = Time(s.time).toMinutes

        if(!v.canTake.contains(p.category)){
          if(verbose){
            println("Category constraint violated for patient " + p.id + " at step" + j + " of vehicle " + v.id + "!")
            println("Patient category: " + p.category)
            println("Vehicle categories: [" + v.canTake.mkString(", ") + "]")
          }
          return false
        }

        if(j > 0 && t < currTime + ist.distMatrix(steps(j-1).place)(s.place)){
          if(verbose){
            println("Travel time constraint between steps " + (j-1) + " and " + j + " of vehicle " + v.id + " violated!")
            println("Solution diff: " + (t - currTime))
            println("arrival " + (j-1) + ": " + steps(j-1).time)
            println("service " + (j-1) + ": " + ist.getPatientById(steps(j-1).patient).srvLen)
            println("arrival " + j + ": " + s.time)
            println("Actual distance: " + ist.distMatrix(steps(j-1).place)(s.place))
          }
          return false
        }

        if(!windows.exists(_.contains(t - ist.distMatrix(v.start)(s.place)))){
          if(verbose){
            println("Travel time constraint between start depot of vehicle " + v.id + " and step " + j + " violated!")
            println("Vehicle has to start at: " + Time(t - ist.distMatrix(v.start)(s.place)))
            println("Availability is: " + windows.mkString(" "))
          }
          return  false
        }

        //Depot
        if(ist.places(s.place).category == 1){
          if (currLoad != 0) {
            if (verbose) println("Vehicle " + v.id + " is not empty at depot " + s.place)
            return false
          }
        }

        else {
          s.operation match {
            //Pickup forward
            case 0 => {
              currLoad += p.load
              if (t < p.rdvStart - Time(ist.maxWaitTime).toMinutes) {
                if (verbose) println("Patient " + p.id + " is taken by vehicle " + v.id + " at " + Time(t) + ", which is too soon before his appointment at " + p.rdvTime)
                return false
              }
            }

            // Drop forward
            case 1 => {
              currLoad -= p.load
              if (t > p.rdvStart - p.srvLen) {
                if (verbose) println("Patient " + p.id + " is dropped by vehicle " + v.id + " at " + Time(t) + ", which is too late for his appointment at " + p.rdvTime)
                return false
              }
            }

            // Pickup backward
            case 2 => {
              currLoad += p.load
              if (t < p.rdvEnd) {
                if (verbose) println("Patient " + p.id + " is taken by vehicle " + v.id + " at " + Time(t) + ", which is too soon before the end of his appointment at " + p.rdvEnd)
                return false
              }
            }

            //Drop backward
            case 3 => {
              currLoad -= p.load
              if (t > p.rdvEnd + Time(ist.maxWaitTime).toMinutes) {
                if (verbose) println("Patient " + p.id + " is dropped by vehicle " + v.id + " at " + Time(t) + ", which is too late after the end of his appointment at " + p.rdvEnd)
                return false
              }
            }
          }

          satisfied(p.id)(s.operation) = v.id
          currTime = t + p.srvLen
        }

        if(currLoad > v.capacity || currLoad < 0){
          if(verbose) println("Capacity of vehicle " + v.id + " is violated at step " + j + " (load: " + currLoad + ", maxCapa: " + v.capacity + ")")
          return false
        }

        if(!windows.exists(_.contains(currTime + ist.distMatrix(s.place)(v.end)))){
          if(verbose){
            println("Travel time constraint between end depot of vehicle " + v.id + " and step " + j + " violated!")
            println("Vehicle will arrive at: " + Time(currTime + ist.distMatrix(s.place)(v.end)))
            println("Availability is: " + windows.mkString(" "))
          }
          return  false
        }
      }
    }

    for(p <- sol.instance.patients){

      if(p.isMandatory && satisfied(p.id)(0) == -1 && satisfied(p.id)(1) == -1 && satisfied(p.id)(2) == -1 && satisfied(p.id)(3) == -1){
        if(softMandatoryCst){
          if(verbose) println("Warning: mandatory patient " + p.id + " not serviced!")
        }
        else{
          if(verbose) println("Mandatory patient " + p.id + " not serviced!")
          return false
        }
      }

      if(satisfied(p.id)(0) != satisfied(p.id)(1) || satisfied(p.id)(2) != satisfied(p.id)(3)){
        if(verbose) println("Inconsistency between service of patient " + p.id + " (different vehicles for same travel: [" + satisfied(p.id).mkString(",") + "])")
        return false
      }
      if(p.start != -1 && p.end != -1 && (
        (satisfied(p.id)(0) == -1 && satisfied(p.id)(2) != -1) || (satisfied(p.id)(0) != -1 && satisfied(p.id)(2) == -1)
      )){
        if(verbose) println("Inconsistency between service of patient " + p.id + " (not all travels serviced: [" + satisfied(p.id).mkString(",") + "])")
        return false
      }
    }

    true
  }
}
