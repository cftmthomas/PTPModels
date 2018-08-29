package modelling

import java.io.{BufferedWriter, File, FileWriter}

import json._
import utils.{SolutionChecker, Time, TimeWindow}

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

/**
  * Greedy construction heuristic.
  *
  * @author Charles Thomas (cftmthomas@gmail.com)
  */
object GreedyModel extends App {

  /* params */

  val silent = false
  val istPath = args(0)
  val instance = JsonParser.readInstance(istPath)
  val istName = instance.name
  val outputPath = if(args.length >= 2) args(1) else "output"
  val solPath = outputPath + "/solutions/GREEDY/" + istName + "_sol.json"
  val logPath = outputPath + "/logs/GREEDY-" + istName + ".log"

  def greedySearch(ist: PTPInstance): Solution = {

    /* data */

    val startTime = 0
    val horizon = 24 * 60
    val maxWaitTime = Time(ist.maxWaitTime).toMinutes

    val nPatient = ist.patients.length
    val nVehicle: Int = ist.vehicles.map(_.availability.length).sum

    val patientRdv: Array[Int] = ist.patients.map(_.rdvStart)
    val patientDur: Array[Int] = ist.patients.map(_.rdvLen)
    val patientSrv: Array[Int] = ist.patients.map(_.srvLen)
    val patientRdvEnd: Array[Int] = ist.patients.map(_.rdvEnd)
    val patientLoad: Array[Int] = ist.patients.map(_.load)

    val (vehicleAvailability, vehicleCapacity, vehicleIndex) =
      ist.vehicles.zipWithIndex.flatMap { case (v, i) => v.availability.map(w => (TimeWindow(w), v.capacity, i)) }.unzip3

    val (vehicleStartWindow, vehicleEndWindow) = vehicleAvailability.map(w => (w.start.toMinutes, w.end.toMinutes)).unzip

    val patientForward: Array[Int] = ist.patients.indices.filter(i => ist.patients(i).start >= 0).toArray
    val patientBackward: Array[Int] = ist.patients.indices.filter(i => ist.patients(i).end >= 0).toArray

    val originForward: Array[Int] = patientForward.map(ist.patients(_).start)
    val destForward: Array[Int] = patientForward.map(ist.patients(_).destination)
    val originBackward: Array[Int] = patientBackward.map(ist.patients(_).destination)
    val destBackward: Array[Int] = patientBackward.map(ist.patients(_).end)

    val startForward: Array[Int] = patientForward.map(p => math.max(ist.patients(p).rdvStart - maxWaitTime, startTime))
    val endForward: Array[Int] = patientForward.map(ist.patients(_).rdvStart)
    val startBackward: Array[Int] = patientBackward.map(ist.patients(_).rdvEnd)
    val endBackward: Array[Int] = patientBackward.map(p => math.min(ist.patients(p).rdvEnd + maxWaitTime, horizon))

    val allPatient: Array[Int] = patientForward ++ patientBackward
    val allOrigin: Array[Int] = originForward ++ originBackward
    val allDest: Array[Int] = destForward ++ destBackward
    val allStart: Array[Int] = startForward ++ startBackward
    val allEnd: Array[Int] = endForward ++ endBackward

    val locationMatrix: Array[Array[Int]] = ist.distMatrix
    val startDepotMatrix: Array[Array[Int]] = Array.tabulate(allOrigin.length, nVehicle)((s, v) => {
      if (ist.vehicles(vehicleIndex(v)).start < 0) 0 else locationMatrix(allOrigin(s))(ist.vehicles(vehicleIndex(v)).start)
    })
    val endDepotMatrix: Array[Array[Int]] = Array.tabulate(allDest.length, nVehicle)((d, v) => {
      if (ist.vehicles(vehicleIndex(v)).end < 0) 0 else locationMatrix(allDest(d))(ist.vehicles(vehicleIndex(v)).end)
    })

    val minTransportTime = allPatient.indices.map(i => locationMatrix(allOrigin(i))(allDest(i)) + patientSrv(allPatient(i)) * 2)


    /* Search */

    val paths = Array.tabulate(nVehicle)(v => {
      val path = ArrayBuffer[Stop]()
      path += Stop(-1, -1, v, 0, 0, vehicleStartWindow(v), 0)
      path
    })

    val requestsPerStartTime = allPatient.indices.sortBy(i => {
      if (i < patientForward.length) patientRdv(allPatient(i)) - minTransportTime(i)
      else patientRdvEnd(allPatient(i))
    })

    val unservicedPatients = mutable.Set[Int]()

    def isForwardTrip(r: Int) = r < patientForward.length

    def isTwoWayPatient(p: Int) = ist.patients(p).start >= 0 && ist.patients(p).end >= 0

    for (r <- requestsPerStartTime /*.filterNot(r => !isForwardTrip(r) && isTwoWayPatient(allPatient(r)) && !patientsServicedForward.contains(allPatient(r)))*/ ) {
      val insertion: Option[(Stop, Stop, Int, Int)] = paths.indices
        .filter(v => ist.vehicles(vehicleIndex(v)).canTake.contains(ist.patients(allPatient(r)).category)) //Filtering compatible vehicles
        .map(v => { //Creating possible insertions
        val lastStop = paths(v).last
        val distance = if (lastStop.isDepot) startDepotMatrix(r)(v) else locationMatrix(lastStop.place)(allOrigin(r))
        val pickup = Stop(r, allPatient(r), allOrigin(r), if (isForwardTrip(r)) 0 else 2, patientSrv(allPatient(r)), math.max(lastStop.departure + distance, allStart(r)), lastStop.load + patientLoad(allPatient(r)))
        val drop = Stop(r, allPatient(r), allDest(r), if (isForwardTrip(r)) 1 else 3, patientSrv(allPatient(r)), pickup.departure + locationMatrix(pickup.place)(allDest(r)), lastStop.load)
        (pickup, drop, distance + minTransportTime(r), v)
      })
        .filter(i => i._2.departure <= math.min(allEnd(r), vehicleEndWindow(i._4) - endDepotMatrix(r)(i._4))) //Filtering insertions that end too late
        .filter(i => i._1.load <= vehicleCapacity(i._4)) //Filtering insertions based on vehicle capacity
        .reduceOption(Ordering.by((_: (Stop, Stop, Int, Int))._3).min) //Selecting insertion that minimizes transport time

      if (insertion.nonEmpty) {
        paths(insertion.get._4) += insertion.get._1
        paths(insertion.get._4) += insertion.get._2
      }
      else if (isTwoWayPatient(allPatient(r))) unservicedPatients += allPatient(r)
    }


    /* Solution */

    val solPaths = Array.fill(ist.vehicles.length) {
      ArrayBuffer[Step]()
    }
    for (p <- paths.indices) {
      paths(p).filterNot(_.isDepot).filterNot(s => unservicedPatients.contains(s.patient)).foreach(s => {
        val v = vehicleIndex(p)
        solPaths(v) += Step(s.place, Time(s.arrival).toString(), ist.patients(s.patient).id, s.operation)
      })
    }

    val sol = Solution(ist, solPaths.zipWithIndex.map { case (steps, i) => Path(ist.vehicles(i).id, steps.toArray.sortBy(_.time)) })
    if(!SolutionChecker.checkSol(sol)) throw new Exception("Invalid solution!")
    sol
  }

  val searchStart = System.nanoTime()
  def timeElapsed: Long = System.nanoTime() - searchStart

  val sol = greedySearch(instance)
  JsonParser.writeSol(solPath, sol)

  val nServiced = sol.nPatientsServiced
  val totalWaitTime = sol.totalWaitingTime

  if(!silent) {
    println("Patients serviced: " + nServiced)
    println("Total waiting time: " + totalWaitTime)
  }

  val outLog = new File(logPath)
  if(!outLog.getParentFile.exists()) outLog.getParentFile.mkdirs()
  outLog.createNewFile()

  val writer = new BufferedWriter(new FileWriter(outLog))
  writer.write(timeElapsed.toDouble/1000000000 + ":[" + nServiced + "," + totalWaitTime + "]")
  writer.close()

  private case class Stop(
                           request: Int,
                           patient: Int,
                           place: Int,
                           operation: Int,
                           var service: Int,
                           var arrival: Int,
                           var load: Int
                         ){
    def isDepot: Boolean = request < 0

    var departure: Int = arrival + service
  }
}