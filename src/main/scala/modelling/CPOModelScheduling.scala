package modelling

import java.io.{BufferedWriter, File, FileWriter}

import ilog.concert._
import ilog.cp._
import json._
import utils.{SolutionChecker, Time, TimeWindow}

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

/**
  * CP Optimizer model. Requires IBM's CPLEX CP Optimizer.
  *
  * @author Charles Thomas (cftmthomas@gmail.com)
  */
object CPOModelScheduling extends App {

  val cp: IloCP = new IloCP()

  /* params */

  val silent = false
  val searchTime = args(0).toInt
  val istPath = args(1)
  val ist = JsonParser.readInstance(istPath)
  val istName = ist.name
  val outputPath = if(args.length >= 3) args(2) else "output"
  val solPath = outputPath + "/solutions/CPOSCHED/" + istName + "_sol.json"
  val logPath = outputPath + "/logs/CPOSCHED-" + istName + ".log"

  val log = ArrayBuffer[(Double, Array[Int])]()


  /* data */

  val startTime = 0
  val endTime = 24 * 60
  val maxWaitTime = Time(ist.maxWaitTime).toMinutes

  val nPatient = ist.patients.length
  val nVehicle: Int = ist.vehicles.map(_.availability.length).sum + 1 //One dummy vehicle (0) added

  val patientRdv: Array[Int] = ist.patients.map(_.rdvStart)
  val patientDur: Array[Int] = ist.patients.map(_.rdvLen)
  val patientSrv: Array[Int] = ist.patients.map(_.srvLen)
  val patientRdvEnd: Array[Int] = ist.patients.map(_.rdvEnd)
  val patientLoad: Array[Int] = ist.patients.map(_.load)

  val (vehicleAvailability, vehicleCap, vehicleIndex) = (
    Array((TimeWindow(Time(startTime), Time(endTime)), patientLoad.sum, -1)) ++ //Dummy
    ist.vehicles.zipWithIndex.flatMap{case (v, i) => v.availability.map(w => (TimeWindow(w), v.capacity, i))} //Others
  ).unzip3

  val (vehicleStartWindow, vehicleEndWindow) = vehicleAvailability.map(w => (w.start.toMinutes, w.end.toMinutes)).unzip

  val patientForward: Array[Int] = ist.patients.indices.filter(i => ist.patients(i).start >= 0).toArray
  val patientBackward: Array[Int] = ist.patients.indices.filter(i => ist.patients(i).end >= 0).toArray

  val originForward: Array[Int] = patientForward.map(ist.patients(_).start)
  val destForward: Array[Int] = patientForward.map(ist.patients(_).destination)

  val originBackward: Array[Int] = patientBackward.map(ist.patients(_).destination)
  val destBackward: Array[Int] = patientBackward.map(ist.patients(_).end)

  val allPatient: Array[Int] = patientForward ++ patientBackward
  val allOrigin: Array[Int] = originForward ++ originBackward
  val allDest: Array[Int] = destForward ++ destBackward

  val locationMatrix: Array[Array[Int]] = ist.distMatrix
  val startDepotMatrix: Array[Array[Int]] = Array.tabulate(allOrigin.length, nVehicle)((s, v) => {
    if(v == 0 || ist.vehicles(vehicleIndex(v)).start < 0) 0 else locationMatrix(allOrigin(s))(ist.vehicles(vehicleIndex(v)).start)
  })
  val endDepotMatrix: Array[Array[Int]] = Array.tabulate(allDest.length, nVehicle)((d, v) => {
    if(v == 0 || ist.vehicles(vehicleIndex(v)).end < 0) 0 else locationMatrix(allDest(d))(ist.vehicles(vehicleIndex(v)).end)
  })

  val minTransportTime = allPatient.indices.map(i => locationMatrix(allOrigin(i))(allDest(i)) + patientSrv(allPatient(i))*2)

  val (forwardMinStart, forwardMaxEnd) = patientForward.indices.map(i =>{
    val p = patientForward(i)
    val earliestPickup = patientRdv(p) - maxWaitTime
    val latestDrop = patientRdv(p) - patientSrv(p)
    (earliestPickup, latestDrop)
  }).unzip

  val (backwardMinStart, backwardMaxEnd) = patientBackward.indices.map(i =>{
    val p = patientBackward(i)
    val latestDrop = patientRdvEnd(p) + maxWaitTime
    val earliestPickup = patientRdvEnd(p)
    (earliestPickup, latestDrop)
  }).unzip

  val allMinStart = forwardMinStart ++ backwardMinStart
  val allMaxEnd = forwardMaxEnd ++ backwardMaxEnd

  val vehicleMapping = Array.fill(ist.vehicles.length)(mutable.Set[Int]())
  vehicleIndex.indices.filter(vehicleIndex(_) >= 0).foreach(i => vehicleMapping(vehicleIndex(i)) += i)
  val vehiclePerId: Map[Int, Set[Int]] = vehicleMapping.zipWithIndex.map{case(indices, v) => (ist.vehicles(v).id, indices.toSet)}.toMap
  val patientPerId: Map[Int, Int] = (0 until nPatient).map(p => (ist.patients(p).id, p)).toMap
  val patientIndexForward = Array.fill(nPatient)(-1)
  val patientIndexBackward = Array.fill(nPatient)(-1)
  patientForward.indices.foreach(i => patientIndexForward(patientForward(i)) = i)
  patientBackward.indices.foreach(i => patientIndexBackward(patientBackward(i)) = patientForward.length + i)
  val activitiesPerPatientId: Map[Int, (Int, Int)] = (patientIndexForward zip patientIndexBackward).zipWithIndex.map{case(activities, index) => (ist.patients(index).id, activities)}.toMap

  def findVehicleByStep(id: Int, s: Step): Int = {
    vehiclePerId(id).foreach(v => {
      if(vehicleAvailability(v).contains(Time(s.time))) return v
    })
    0
  }

  var lb = 0


  /* variables */

  //Activity variables:
  val forwardActivities = Array.fill(patientForward.length)(cp.intervalVar(0, maxWaitTime))
  val backwardActivities = Array.fill(patientBackward.length)(cp.intervalVar(0, maxWaitTime))
  val allActivities = forwardActivities ++ backwardActivities

  for(i <- patientForward.indices){
    val a = forwardActivities(i)
    val p = patientForward(i)
    val earliestPickup = patientRdv(p) - maxWaitTime
    val latestDrop = patientRdv(p) - patientSrv(p)

    a.setStartMin(earliestPickup)
    a.setEndMax(latestDrop)

    a.setOptional()
  }

  for(i <- patientBackward.indices){
    val a = backwardActivities(i)
    val p = patientBackward(i)
    val latestDrop = patientRdvEnd(p) + maxWaitTime
    val earliestPickup = patientRdvEnd(p)

    a.setStartMin(earliestPickup)
    a.setEndMax(latestDrop)

    a.setOptional()
  }

  //Auxiliary vars for travel time constraints
  val allStops: Array[IloIntervalVar] = Array.tabulate(allActivities.length*2)(s =>{
    val i = s%allActivities.length
    val stopVar = cp.intervalVar(patientSrv(allPatient(i)))

    if(s < allActivities.length) cp.add(cp.eq(cp.startOf(allActivities(i)), cp.startOf(stopVar)))
    else cp.add(cp.eq(cp.endOf(allActivities(i)), cp.startOf(stopVar)))

    stopVar
  })
  val allPlace: Array[Int] = allOrigin ++ allDest

  val vehicleForward = patientForward.map(p => cp.intVar(
    Array(0) ++ (1 until nVehicle).filter(v => ist.vehicles(vehicleIndex(v)).canTake.contains(ist.patients(p).category))
  ))
  val vehicleBackward = patientBackward.map(p => cp.intVar(
    Array(0) ++ (1 until nVehicle).filter(v => ist.vehicles(vehicleIndex(v)).canTake.contains(ist.patients(p).category))
  ))

  val allVehicle = vehicleForward ++ vehicleBackward

//  //Transport time for patients:
//  val actualTransportTime = Array.fill(allPatient.length)(cp.intVar(0, maxWaitTime))
//  val actualTransportTime = allPatient.indices.map(i => {
//    if(i < patientForward.length) -allStart(i) + patientRdv(allPatient(i))
//    else (allEnd(i) + patientSrv(allPatient(i))) - patientRdvEnd(allPatient(i))
//  })
//
//  val travelWaitTime: Array[IloIntVar] = Array.tabulate(allPatient.length)(i =>{
//    if(actualTransportTime(i).getMax < minTransportTime(i)) cp.intVar(0, 0)
//    else cp.intVar(0, maxWaitTime - minTransportTime(i))
//  })

  val served: Array[IloConstraint] = allActivities.map(a => cp.presenceOf(a))
  val visited: Array[IloIntVar] = Array.fill(nPatient)(cp.boolVar())

  val consumptionIntervals = Array.fill(nVehicle)(Array.fill(allActivities.length)(cp.intervalVar(0, maxWaitTime)))
  val vehicleConsumption = Array.fill(nVehicle)(cp.cumulFunctionExpr())


  /* constraints */

  //Linking service of patients
  for(p <- 0 until nPatient){
    activitiesPerPatientId(ist.patients(p).id) match{
      case (-1, a2) => cp.add(cp.eq(visited(p), served(a2)))
      case (a1, -1) => cp.add(cp.eq(visited(p), served(a1)))
      case (a1, a2) =>
        cp.add(cp.eq(visited(p), cp.and(served(a1), served(a2))))
        cp.add(cp.eq(served(a1), served(a2)))
    }
  }

  for(i <- allPatient.indices) {
    val p = allPatient(i)

    //If the patient is visited:

    cp.add(cp.eq(served(i), cp.neq(allVehicle(i), 0))) // Real vehicle assigned

    //Depot travel time and vehicle availability taken into account:
    val minStartTime = cp.element(vehicleIndex.indices.map(v => vehicleStartWindow(v) + startDepotMatrix(i)(v)).toArray, allVehicle(i))
    val maxEndTime = cp.element(vehicleIndex.indices.map(v => vehicleEndWindow(v) - endDepotMatrix(i)(v) - patientSrv(p)).toArray, allVehicle(i))
    cp.add(cp.ifThen(cp.eq(visited(p), 1), cp.ge(cp.startOf(allActivities(i)), minStartTime)))
    cp.add(cp.ifThen(cp.eq(visited(p), 1), cp.le(cp.endOf(allActivities(i)), maxEndTime)))

//    cp.add(cp.ifThenElse(
//      visited(p),
//      cp.eq(travelWaitTime(i), cp.sum(actualTransportTime(i), -minTransportTime(i))),
//      cp.eq(travelWaitTime(i), 0)
//    ))
  }

  //Setting up travel times between activities:
  for (i <- allStops.indices; j <- allStops.indices) {
    if (i != j) {
      val iActivity: Int = i%allActivities.length
      val jActivity: Int = j%allActivities.length

      cp.add(cp.ifThen(
        cp.and(cp.eq(allVehicle(iActivity), allVehicle(jActivity)), cp.neq(allVehicle(iActivity), 0)),
        cp.or(
          cp.le(cp.sum(cp.endOf(allStops(i)), locationMatrix(allPlace(i))(allPlace(j))), cp.startOf(allStops(j))),
          cp.le(cp.sum(cp.endOf(allStops(j)), locationMatrix(allPlace(j))(allPlace(i))), cp.startOf(allStops(i)))
        )
      ))
    }
  }

  //linking vehicles and consumption intervals:
  for(v <- 0 until nVehicle){
    for(i <- consumptionIntervals(v).indices){
      val activity = allActivities(i)
      val consActivity = consumptionIntervals(v)(i)
      consActivity.setOptional()
      cp.add(cp.ifThen(cp.and(cp.presenceOf(activity), cp.eq(allVehicle(i), v)), cp.presenceOf(consActivity)))
//      cp.add(cp.eq(cp.and(cp.presenceOf(activity), cp.eq(allVehicle(i), v)), cp.presenceOf(consActivity))) //Cons activity present iff activity present and vehicle selected
      cp.add(cp.ifThen(cp.and(cp.presenceOf(activity), cp.eq(allVehicle(i), v)),cp.eq(cp.startOf(activity), cp.startOf(consActivity)))) //Synchronizing starts
      cp.add(cp.ifThen(cp.and(cp.presenceOf(activity), cp.eq(allVehicle(i), v)),cp.eq(cp.endOf(activity), cp.endOf(consActivity)))) //Synchronizing ends
    }
  }

  //Setting up cumulative function for vehicles:
  for(v <- 1 until nVehicle) {
    for(i <- consumptionIntervals(v).indices){
      vehicleConsumption(v) = cp.sum(vehicleConsumption(v), cp.pulse(consumptionIntervals(v)(i), patientLoad(allPatient(i))))
    }
    cp.add(cp.le(vehicleConsumption(v), vehicleCap(v)))
  }


  /* Objective function */

  val nServed = cp.sum(visited.map(cp.prod(_, 1)))

  //Waiting time:
//  val totalWaitTime = cp.sum(travelWaitTime.map(cp.prod(_, 1))) //Total waiting time of patients (to minimize)
//  //  val maxTravelWaitTime: CPIntVar = maximum(travelWaitTime) //Maximum waiting time among patients (to minimize)

//  val objFunctions: Array[IloIntExpr] = Array(
//    cp.negative(nServed),
//    totalWaitTime
//  )

  val objFunctions: Array[IloIntExpr] = Array(
    nServed
  )

  val objectives: Array[IloObjective] = objFunctions.map(cp.maximize)

  /* Solution management */

  //sol tracking:
  var currentSol = cp.solution()

  //On solution:
  def onSolution(): Unit = {

    //Printing sol:
    if(!silent) {
//      println("Selected patients: " + visited.mkString(" "))
//      println("Vehicle assigned forward: " + vehicleForward.mkString(" "))
//      println("Vehicle assigned backward: " + vehicleBackward.mkString(" "))
//      println("Start Forward: " + startForward.mkString(" "))
//      println("End Forward: " + endForward.mkString(" "))
//      println("Start Backward: " + startBackward.mkString(" "))
//      println("end Backward: " + endBackward.mkString(" "))
//      println("travel waiting time: " + travelWaitTime.indices.filter(i => visited(allPatient(i)).isTrue).map(travelWaitTime(_)).mkString(" "))

      println("Patients serviced: " + cp.getValue(nServed).toInt)
//      println("Total waiting time: " + Time(cp.getValue(totalWaitTime).toInt))
//      println("Max travel waiting time: " + Time(maxTravelWaitTime.value))

//      allPatient.indices.filter(i => visited(allPatient(i)).isTrue).sortBy(i => allStart(i).value).foreach(i => {
//        print(if (i < patientForward.length) "Forward" else "Backward")
//        print(" travel (id: " + i)
//        print(") for patient " + allPatient(i))
//        print(" of duration " + allDuration(i).value)
//        print(" and load " + patientLoad(allPatient(i)))
//        print(" is executed on vehicle " + allVehicle(i).value)
//        print(" at time " + TimeWindow(Time.intToTime(allStart(i).value), Time.intToTime(allEnd(i).value)))
//        println(" (rdv was at " + TimeWindow(Time(ist.patients(allPatient(i)).rdvTime), Time(ist.patients(allPatient(i)).rdvEnd)) + ")")
//      })
//      println()

      println("------------")
    }

    //Checking and saving sol:
    val paths = Array.fill(ist.vehicles.length)(ArrayBuffer[Step]())
    allActivities.indices.filter(a => cp.isPresent(allActivities(a))).foreach(i => {
      val v = vehicleIndex(cp.getValue(allVehicle(i)).toInt)
      val forward = i < patientForward.length
      paths(v) += Step(allOrigin(i), Time(cp.getStart(allActivities(i))).toString(), ist.patients(allPatient(i)).id, if(forward) 0 else 2)
      paths(v) += Step(allDest(i), Time(cp.getEnd(allActivities(i))).toString(), ist.patients(allPatient(i)).id, if(forward) 1 else 3)
    })

    val sol = Solution(ist, paths.zipWithIndex.map{case (steps, i) => Path(ist.vehicles(i).id, steps.toArray.sortBy(_.time))})

    if(!SolutionChecker.checkSol(sol)) throw new Exception("Invalid solution!")
    JsonParser.writeSol(solPath, sol)

    //Logging objectives:
    log += ((timeElapsed.toDouble/1000000000, Array(cp.getValue(nServed).toInt/*, cp.getValue(totalWaitTime).toInt*/)))

    //Recording sol:
    currentSol = cp.solution()
  }

  def assignSol(sol: Solution): Unit = {
    val cpoSol = cp.solution()
    val requestServiced = mutable.Set[Int]()

    for(solPath <- sol.paths){
      val vid = solPath.vehicle
      for(s <- solPath.steps){
        val p = patientPerId(s.patient)
        val r = if(s.operation < 2) activitiesPerPatientId(s.patient)._1 else activitiesPerPatientId(s.patient)._2
        val v = findVehicleByStep(vid, s)

        requestServiced += r

        cpoSol.setPresent(allActivities(r))
        cpoSol.setValue(allVehicle(r), v)
        if(s.operation == 0 || s.operation == 2) cpoSol.setStart(allActivities(r), Time(s.time).toMinutes)
        else cpoSol.setEnd(allActivities(r), Time(s.time).toMinutes)
      }
    }
    for(r <- allActivities.indices) if(!requestServiced.contains(r)) cpoSol.setAbsent(allActivities(r))

    lb = sol.nPatientsServiced

    cp.setStartingPoint(cpoSol)
  }

  def setSolFromFile(path: String): Unit = {
    val sol = JsonParser.readSol(path)
    assignSol(sol)
  }


  /* Search */

  def basicSearch(): Unit = {
    cp.setParameter(IloCP.DoubleParam.TimeLimit, searchTime)
    cp.setParameter(IloCP.IntParam.Workers, 1)
    if(silent) cp.setOut(null)
    cp.startNewSearch()
    while(cp.next()){
      onSolution()
    }
    cp.end()
  }

  //Greedy search
  def greedySearch(): Unit = {
    val greedySol = GreedyModel.greedySearch(ist)
    assignSol(greedySol)
  }

  //Search for each objective:
  val searches: Array[() => Unit] = Array(
    () => basicSearch(),
    () => basicSearch()
  )

  //Lexicographical search:
  def lexSearch(): Unit = {
    for (i <- objectives.indices) {

      //Setting up objectives:
      for (o <- objectives.indices) {
        if (o == i-1){
          cp.remove(objectives(o))
          cp.add(cp.ge(objFunctions(o), cp.getValue(objFunctions(o))))
        }
        else if (o == i) cp.add(objectives(o))
      }

      //Starting search:
      if(!silent) println("starting search on objective " + i)

      searches(i)()
    }
  }

  def setFirstSol(): Unit = {
    if (!silent) println("first sol")
    greedySearch()
//    setSolFromFile("data/startSols/" + istName + "_sol.json")
  }


  /* Execution */

  if(!silent) println("starting search")
  val searchStart = System.nanoTime()

  setFirstSol()
  lexSearch()

  if(!silent) println("search done")

  if(log.nonEmpty) log += log.last

  val outLog = new File(logPath)
  if(!outLog.getParentFile.exists()) outLog.getParentFile.mkdirs()
  outLog.createNewFile()

  val writer = new BufferedWriter(new FileWriter(outLog))
  writer.write(log.map{case (t, objsVals) => t + ":[" + objsVals.mkString(",") + "]"}.mkString("\n"))
  writer.close()

  def timeElapsed: Long = System.nanoTime() - searchStart
}