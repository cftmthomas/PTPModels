package modelling

import java.io.{BufferedWriter, File, FileWriter}

import json._
import oscar.algo.Inconsistency
import oscar.algo.search.Branching
import oscar.cp._
import oscar.cp.core.CPSol
import _root_.search.BasicLNS
import utils.{SolutionChecker, Time, TimeWindow}

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer
import scala.util.Random

/**
  * Basic Scheduling model.
  *
  * @author Charles Thomas (cftmthomas@gmail.com)
  */
object SchedulingModel extends CPModel with App {

  /* params */

  solver.silent = false
  val searchTime = args(0).toInt
  val istPath = args(1)
  val ist = JsonParser.readInstance(istPath)
  val istName = ist.name
  val outputPath = if(args.length >= 3) args(2) else "output"
  val solPath = outputPath + "/solutions/SCHED/" + istName + "_sol.json"
  val logPath = outputPath + "/logs/SCHED-" + istName + ".log"

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


  /* Variables */

  val visited: Array[CPBoolVar] = Array.fill(nPatient)(CPBoolVar())

  val (startForward, endForward, durForward) = patientForward.map(ist.patients(_)).map(p =>{
    val start = CPIntVar(math.max(0, p.rdvStart - maxWaitTime) to p.rdvStart)
    val end = CPIntVar(math.max(0, p.rdvStart - maxWaitTime) to p.rdvStart)
    (start, end, end-start)
  }).unzip3

  val (startBackward, endBackward, durBackward) = patientBackward.map(ist.patients(_)).map(p =>{
    val start = CPIntVar(p.rdvEnd to math.min(endTime, p.rdvEnd + maxWaitTime))
    val end = CPIntVar(p.rdvEnd to math.min(endTime, p.rdvEnd + maxWaitTime))
    (start, end, end-start)
  }).unzip3

  val allStart: Array[CPIntVar] = startForward ++ startBackward // duplicated variables
  val allEnd: Array[CPIntVar] = endForward ++ endBackward // duplicated variables
  val allDuration: Array[CPIntVar] = durForward ++ durBackward // duplicated variables

  //Auxiliary vars for travel time constraints
  val allArrival: Array[CPIntVar] = allStart ++ allEnd
  val allDeparture: Array[CPIntVar] = allArrival.indices.map(i => allArrival(i) + patientSrv(allPatient(i%allStart.length)))
  val allPlace: Array[Int] = allOrigin ++ allDest

  val vehicleForward: Array[CPIntVar] = patientForward.map(p => CPIntVar(
    Array(0) ++ (1 until nVehicle).filter(v => ist.vehicles(vehicleIndex(v)).canTake.contains(ist.patients(p).category))
  ))
  val vehicleBackward: Array[CPIntVar] = patientBackward.map(p => CPIntVar(
    Array(0) ++ (1 until nVehicle).filter(v => ist.vehicles(vehicleIndex(v)).canTake.contains(ist.patients(p).category))
  ))

  val allVehicle: Array[CPIntVar] = vehicleForward ++ vehicleBackward

  val loadVar = allPatient.map(p => CPIntVar(patientLoad(p)))

  //Transport time for patients:
  val actualTransportTime = allPatient.indices.map(i => {
    if(i < patientForward.length) -allStart(i) + patientRdv(allPatient(i))
    else (allEnd(i) + patientSrv(allPatient(i))) - patientRdvEnd(allPatient(i))
  })

  val travelWaitTime = Array.tabulate[CPIntVar](allPatient.length)(i =>{
    if(actualTransportTime(i).getMax < minTransportTime(i)) CPIntVar(0)
    else CPIntVar(0 to actualTransportTime(i).getMax - minTransportTime(i))
  })


  /* constraints */

  for (d <- allDuration) add(d >= 0)

  for(i <- allPatient.indices) {
    val p = allPatient(i)

    //If the patient is visited:

    add(visited(p) === (allVehicle(i) ?!== 0)) // Real vehicle assigned

    //Depot travel time and vehicle availability taken into account:
    add(visited(p) ==> (allStart(i) ?>= (vehicleStartWindow(allVehicle(i)) + startDepotMatrix(i)(allVehicle(i)))))
    add(visited(p) ==> (allEnd(i) ?<= (vehicleEndWindow(allVehicle(i)) - (endDepotMatrix(i)(allVehicle(i)) + patientSrv(p)))))

    //Rdv start and end taken into account:
    if(i < patientForward.length) add(visited(p) ==> (allEnd(i) ?<= patientRdv(p) - patientSrv(p)))
    else add(visited(p) ==> (allStart(i) ?>= patientRdv(p) + patientDur(p)))

    add(visited(p) ==> (travelWaitTime(i) ?=== (actualTransportTime(i) - minTransportTime(i))))

    //If the patient is not visited:

    add(!visited(p) ==> (allDuration(i) ?=== 0)) //Duration set to 0

    //Start time set to rdv time
    if(i < startForward.length) add(!visited(p) ==> (allStart(i) ?=== allStart(i).getMax))
    else add(!visited(p) ==> (allStart(i) ?=== allStart(i).getMin))

    add(!visited(p) ==> (travelWaitTime(i) ?=== 0))
  }

  for (i <- allArrival.indices; j <- allArrival.indices) {
    if (i != j) {
      val iActivity: Int = i%allStart.length
      val jActivity: Int = j%allStart.length

      add(((allVehicle(iActivity) ?=== allVehicle(jActivity)) && (allVehicle(iActivity) ?!== 0)) ==> (
          (allDeparture(i) + locationMatrix(allPlace(i))(allPlace(j)) ?<= allArrival(j)) ||
          (allDeparture(j) + locationMatrix(allPlace(j))(allPlace(i)) ?<= allArrival(i))
      ))
    }
  }

  for(i <- 1 until nVehicle) {
    val capVar = CPIntVar(vehicleCap(i))
    add(maxCumulativeResource(allStart,allDuration,allEnd,loadVar,allVehicle,capVar,i))
  }


  /* Objective function */

  val nServed = sum(visited)

  //Waiting time:
  val totalWaitTime: CPIntVar = sum(travelWaitTime) //Total waiting time of patients (to minimize)
//  val maxTravelWaitTime: CPIntVar = maximum(travelWaitTime) //Maximum waiting time among patients (to minimize)

  solver.minimize(-nServed, totalWaitTime)
//  maximize(nServed)


  /* Solution management */

  //sol tracking:
  var currentSol: CPSol = new CPSol(Set[CPIntVar]())

  //On solution:
  onSolution {

    //Printing sol:
    if(!solver.silent) {
//      println("Selected patients: " + visited.mkString(" "))
//      println("Vehicle assigned forward: " + vehicleForward.mkString(" "))
//      println("Vehicle assigned backward: " + vehicleBackward.mkString(" "))
//      println("Start Forward: " + startForward.mkString(" "))
//      println("End Forward: " + endForward.mkString(" "))
//      println("Start Backward: " + startBackward.mkString(" "))
//      println("end Backward: " + endBackward.mkString(" "))
//      println("travel waiting time: " + travelWaitTime.indices.filter(i => visited(allPatient(i)).isTrue).map(travelWaitTime(_)).mkString(" "))

      println("Patients serviced: " + nServed)
      println("Total waiting time: " + Time(totalWaitTime.value))
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
    val paths = Array.fill(ist.vehicles.length){ArrayBuffer[Step]()}
    for(i <- allPatient.indices.filter(i => visited(allPatient(i)).isTrue)){
      val v = vehicleIndex(allVehicle(i).value)
      val forward = i < patientForward.length
      paths(v) += Step(allOrigin(i), Time(allStart(i).value).toString(), ist.patients(allPatient(i)).id, if(forward) 0 else 2)
      paths(v) += Step(allDest(i), Time(allEnd(i).value).toString(), ist.patients(allPatient(i)).id, if(forward) 1 else 3)
    }
    val sol = Solution(ist, paths.zipWithIndex.map{case (steps, i) => Path(ist.vehicles(i).id, steps.toArray.sortBy(_.time))})

    if(!SolutionChecker.checkSol(sol)) throw new Exception("Invalid solution!")
    JsonParser.writeSol(solPath, sol)

    //Logging objectives:
    log += ((timeElapsed.toDouble/1000000000, solver.objective.objs.map(o => math.abs(o.best)).toArray))

    //Recording sol:
    currentSol = new CPSol(decVars.toSet)
  }

  def assignSol(sol: Solution): Boolean = {
    var consistent = true
    for(solPath <- sol.paths){
      val vid = solPath.vehicle
      for(s <- solPath.steps){
        val p = patientPerId(s.patient)
        val r = if(s.operation < 2) activitiesPerPatientId(s.patient)._1 else activitiesPerPatientId(s.patient)._2
        val v = findVehicleByStep(vid, s)

        add(visited(p) === 1)
        add(allVehicle(r) === v)
        if(!(visited(p).isBound && allVehicle(r).isBound)){
          if(!solver.silent) println("Unable to assign step " + s + " of vehicle " + vid)
          consistent = false
        }
        if(s.operation == 0 || s.operation == 2){
          add(allStart(r) === Time(s.time).toMinutes)
          if(!allStart(r).isBound){
            if(!solver.silent) println("Unable to assign step " + s + " of vehicle " + vid)
            consistent = false
          }
        }
        else{
          add(allEnd(r) === Time(s.time).toMinutes)
          if(!allEnd(r).isBound){
            if(!solver.silent) println("Unable to assign step " + s + " of vehicle " + vid)
            consistent = false
          }
        }
      }
    }

    for(pv <- visited){
      if(!pv.isBound) pv.assignFalse()
    }

    for(wt <- travelWaitTime){
      if(!wt.isBound) add(wt === 0)
    }

    consistent
  }

  def setSolFromFile(path: String): Unit = {
    val sol = JsonParser.readSol(path)
    if(!assignSol(sol)) throw new Exception("solution inconsistent!")
  }


  /* Visualisation */

  //  //Gant + load
  //  val frame = new VisualFrame("CSD Problem", nVehicle + 1, 1)
  //  val colors = VisualUtil.getRandomColors(nPatient + nVehicle, pastel = true)
  //  val gantt = new VisualGanttChart(allStart, allDuration, allEnd, i => i, colors = i => colors(allPatient(i)))
  //
  //  val profiles = Array.tabulate(nVehicle)(r => new VisualProfile(allStart, allDuration, allEnd, loadVar ++ loadVar, allVehicle, vehicleCap(r), r, color = colors(nPatient + r)))
  //
  //  onSolution {
  //    gantt.update(1, 20)
  //    profiles.foreach(_.update(1, 20))
  //  }
  //
  //  frame.createFrame("Gantt chart").add(gantt)
  //  for (r <- 0 until nVehicle) frame.createFrame("Vehicle "+r).add(profiles(r))
  //  frame.pack()


  /* Search */

  //Heuristic sub methods:
  def slackPatientForward(i: Int) = if (ist.patients(i).start >= 0) locationMatrix(ist.patients(i).start)(ist.patients(i).destination) else 0
  def slackPatientBackward(i: Int) = if (ist.patients(i).end >= 0) locationMatrix(ist.patients(i).destination)(ist.patients(i).end) else 0
  def minConsoPatient(i: Int) = (slackPatientBackward(i) + slackPatientBackward(i)) * patientLoad(i)
  def vehicleUsage(i: Int) = allVehicle.count(v => v.isBoundTo(i))

  val decVars = allVehicle ++ allStart ++ allEnd

  //Search heuristic:
  val varHeuris = (i: Int) => {
    val p = if(i < allVehicle.length) allPatient(i)
    else if(i < allVehicle.length*2) allPatient(i - allVehicle.length)
    else allPatient(i - allVehicle.length*2)

    -minConsoPatient(p)
  }

  val valHeuris = (i: Int) => {
    if(i < allVehicle.length) allVehicle(i).filter(_ > 0).minBy(vehicleUsage)
    else{
      val p = if(i < allVehicle.length*2) allPatient(i - allVehicle.length) else allPatient(i - allVehicle.length*2)

      if(decVars(i).max <= patientRdv(p)) decVars(i).max
      else decVars(i).min
    }
  }

  val customSearch: Branching = conflictOrderingSearch(decVars, varHeuris, valHeuris)

  //Relaxes randomly relaxSize% of the patients
  val randomRelax = (sol: CPSol, relaxSize: Double) => {
    val nFix = allVehicle.length - (relaxSize * allVehicle.length).ceil.toInt

    val varArray = allVehicle.indices.toArray //map to real indice of variable
    var boundStart = varArray.length //Elements of varArray from this index are bound

    while(allVehicle.count(_.isBound) < nFix){
      val i = Random.nextInt(boundStart) //Selecting new decision var to freeze randomly
      val j = varArray(i)

      //Freezing decision var and optional vars
      val v = allVehicle(j)
      val s = allStart(j)
      val e = allEnd(j)
      add(v === sol(v))
      add(s === sol(s))
      add(e === sol(e))
      if(!(v.isBound && s.isBound && e.isBound)) throw Inconsistency

      //marking var as bound:
      boundStart -= 1
      varArray(i) = varArray(boundStart)
      varArray(boundStart) = j
    }
  }

  //LNS:
  def lns(time: Int): Unit = {

    val nBkts = 1000
    val relaxSize = math.min(1.0, 10.0/nPatient)
    val nIters = Int.MaxValue

    val searchEngine = BasicLNS(solver, decVars)

    searchEngine.setSol(currentSol)

    //Starting LNS:
    searchEngine.search(randomRelax, customSearch, time * 1000000000L, nIters, relaxSize, nBkts)
  }

  //Complete timed search
  def basicSearch(time: Int): Unit = {
    search(customSearch)
    val stats = start(Int.MaxValue, Int.MaxValue, time)
    if(!solver.silent) println(stats)
  }

  //Greedy search
  def greedySearch(): Unit = {
    val greedySol = GreedyModel.greedySearch(ist)
    if(!assignSol(greedySol)) throw new Exception("Greedy solution inconsistent!")
  }

  //Search for each objective:
  val searches = Array(
    () => lns(searchTime - (timeElapsed/1000000000).toInt),
    () => lns(searchTime - (timeElapsed/1000000000).toInt)
  )

  //Lexicographical search:
  def lexSearch(): Unit = {
    for (i <- solver.objective.objs.indices) {

      //Setting up objectives:
      for (o <- solver.objective.objs.indices) {
        val obj = solver.objective.objs(o)
        if (o < i) obj.tightenMode = TightenType.WeakTighten
        else if (o == i) obj.tightenMode = TightenType.StrongTighten
        else obj.tightenMode = TightenType.NoTighten
      }

      //Starting search:
      if(!solver.silent) println("starting search on objective " + i)

      searches(i)()
    }
  }

  def setFirstSol(): Unit = {
    if (!solver.silent) println("first sol")

    val stats = solver.startSubjectTo(nSols = 1, failureLimit = Int.MaxValue, timeLimit = searchTime) {
      greedySearch()
//      setSolFromFile("data/startSols/" + istName + "_sol.json")

      search(binaryFirstFail(decVars))
    }

    if (!solver.silent) println(stats)
  }


  /* Execution */

//  println("Selected request: " + visited.mkString(" "))
//  println("Vehicle assigned: " + allVehicle.mkString(" "))
//  println("Start: " + allStart.mkString(" "))
//  println("End: " + allEnd.mkString(" "))
//  println("Duration: " + allDuration.mkString(" "))
//  println("Patient service: " + patientSrv.mkString(" "))
//  println("Location matrix: " + locationMatrix.map(_.mkString(" ")).mkString("\n"))

  if(!solver.silent) println("starting search")
  val searchStart = System.nanoTime()

  setFirstSol()
  lexSearch()

  if(!solver.silent) println("search done")

  log += ((timeElapsed.toDouble/1000000000, solver.objective.objs.map(o => math.abs(o.best)).toArray))

  val outLog = new File(logPath)
  if(!outLog.getParentFile.exists()) outLog.getParentFile.mkdirs()
  outLog.createNewFile()

  val writer = new BufferedWriter(new FileWriter(outLog))
  writer.write(log.map{case (t, objsVals) => t + ":[" + objsVals.mkString(",") + "]"}.mkString("\n"))
  writer.close()

  def timeElapsed: Long = System.nanoTime() - searchStart
}