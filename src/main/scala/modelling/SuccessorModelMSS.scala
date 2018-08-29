package modelling

import java.io.{BufferedWriter, File, FileWriter}

import json.JsonParser
import oscar.algo.Inconsistency
import oscar.algo.search.Branching
import oscar.cp._
import oscar.cp.core.CPSol
import _root_.search.OptionalSelectionLNS
import utils.{SolutionChecker, Time, TimeWindow}

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer
import scala.util.Random

/**
  * Circuit based Successor model.
  *
  * @author Charles Thomas (cftmthomas@gmail.com)
  */
object SuccessorModelMSS extends CPModel with App{

  /* params */

  solver.silent = false
  val searchTime = args(0).toInt
  val istPath = args(1)
  val ist = JsonParser.readInstance(istPath)
  val istName = ist.name
  val outputPath = if(args.length >= 3) args(2) else "output"
  val solPath = outputPath + "/solutions/SUCCMSS/" + istName + "_sol.json"
  val logPath = outputPath + "/logs/SUCCMSS-" + istName + ".log"

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

  //Vehicles availability and index
  val (vehicleAvailability, capacities, vehicleIndex) = (
    Array((TimeWindow(Time(startTime), Time(endTime)), patientLoad.sum, -1)) ++ //Dummy
      ist.vehicles.zipWithIndex.flatMap{case (v, i) => v.availability.map(w => (TimeWindow(w), v.capacity, i))} //Others
    ).unzip3

  val (vehicleStartWindow, vehicleEndWindow) = vehicleAvailability.map(w => (w.start.toMinutes, w.end.toMinutes)).unzip

  val stopBuffer = ArrayBuffer[Stop]()
  val travelBuffer = ArrayBuffer[(Int, Int, Boolean)]() //stop1 (id), stop2 (id), forward

  //Generating stops for each patient:
  for(i <- ist.patients.indices){
    val patient = ist.patients(i)

    if(patient.start >= 0){
      stopBuffer += Stop(i, patient.start, math.max(startTime, patient.rdvStart - maxWaitTime), patient.rdvStart, 0)
      stopBuffer += Stop(i, patient.destination, math.max(startTime, patient.rdvStart - maxWaitTime), patient.rdvStart, 1)
      travelBuffer += ((stopBuffer.size-2, stopBuffer.size-1, true))
    }

    if(patient.end >= 0){
      stopBuffer += Stop(i, patient.destination, patient.rdvEnd, math.min(endTime, patient.rdvEnd + maxWaitTime), 2)
      stopBuffer += Stop(i, patient.end, patient.rdvEnd, math.min(endTime, patient.rdvEnd + maxWaitTime), 3)
      travelBuffer += ((stopBuffer.size-2, stopBuffer.size-1, false))
    }
  }

  val nStop = stopBuffer.length

  //Generating stops for start depots:
  for(v <- vehicleIndex.indices){
    if(vehicleIndex(v) < 0) stopBuffer += Stop(-1, -1, startTime, endTime, 0)
    else stopBuffer += Stop(-1, ist.vehicles(vehicleIndex(v)).start, math.max(startTime, vehicleStartWindow(v)), vehicleEndWindow(v), 0)
  }

  //Generating stops for end depots:
  for(v <- vehicleIndex.indices){
    if(vehicleIndex(v) < 0) stopBuffer += Stop(-1, -1, startTime, endTime, 3)
    else stopBuffer += Stop(-1, ist.vehicles(vehicleIndex(v)).end, math.max(startTime, vehicleStartWindow(v)), vehicleEndWindow(v), 3)
  }

  val sites = stopBuffer.toArray
  val travels = travelBuffer.toArray

  val nSite = sites.length

  //Computing distance matrix:
  val distances: Array[Array[Int]] = Array.tabulate(nSite, nSite)((i, j) => {
    val pi = sites(i).place
    val pj = sites(j).place
    if(pi == pj) 0
    else if(pi == -1 || pj == -1) 0 //dist to dummy depot is always 0
    else ist.distMatrix(pi)(pj)
  })

  val maxCapacity: Int = capacities.max

  val minTransportTime = travels.map{case (stop1, stop2, _) => distances(stop1)(stop2) + sites(stop1).service*2}

  val vehicleMapping = Array.fill(ist.vehicles.length)(mutable.Set[Int]())
  vehicleIndex.indices.filter(vehicleIndex(_) >= 0).foreach(i => vehicleMapping(vehicleIndex(i)) += i)
  val vehiclePerId: Map[Int, Set[Int]] = vehicleMapping.zipWithIndex.map{case(indices, v) => (ist.vehicles(v).id, indices.toSet)}.toMap
  val patientPerId: Map[Int, Int] = (0 until nPatient).map(p => (ist.patients(p).id, p)).toMap

  val stopByOperation: Array[Array[Int]] = Array.fill(nPatient)(Array.fill(4)(-1))
  for(i <- 0 until nStop) stopByOperation(sites(i).patient)(sites(i).operation) = i

  def findStopByStep(step: Step): Int = stopByOperation(patientPerId(step.patient))(step.operation)

  def findVehicleByStep(id: Int, s: Step): Int = {
    vehiclePerId(id).foreach(v => {
      if(vehicleAvailability(v).contains(Time(s.time))) return v
    })
    0
  }


  /* Variables */

  val pred: Array[CPIntVar] = Array.fill(nSite)(CPIntVar(0 until nSite)) //Predecessor
  val succ: Array[CPIntVar] = Array.fill(nSite)(CPIntVar(0 until nSite)) //Successor

  //Which vehicle goes to each site:
  val vehicle: Array[CPIntVar] = Array.tabulate(nSite)(i => {
    if(i < nStop) CPIntVar.sparse(
      //Considering only compatible vehicles
      vehicleIndex.indices.filter(v => v == 0 || ist.vehicles(vehicleIndex(v)).canTake.contains(sites(i).category))
    )
    else CPIntVar((i-nStop)%nVehicle) //Only assigned vehicle for depots
  })

  //Arrival time at each site:
  val arrival: Array[CPIntVar] = Array.tabulate(nSite)(i => {
    CPIntVar(sites(i).winStart to sites(i).winEnd)
  })

  val duration: Array[CPIntVar] = Array.tabulate(nSite)(i => {
    CPIntVar(Array(sites(i).service, 0))
  })

  //Departure time at each site:
  val departure: Array[CPIntVar] = Array.tabulate(nSite)(i => arrival(i) + duration(i))

  //Load of each vehicle after each site:
  val load: Array[CPIntVar] = Array.tabulate(nSite)(i => {
    if(i < nStop) CPIntVar(0, maxCapacity)
    else CPIntVar(0) //Must be zero at depot -> no patient forgotten in the vehicle!
  })

  //Stops and patients serviced:
  val stopServiced: Array[CPBoolVar] = Array.fill(nStop)(CPBoolVar())
  val patientServiced: Array[CPBoolVar] = Array.fill(nPatient)(CPBoolVar())

  //Travels
  val travelStart = travels.map(t => arrival(t._1))
  val travelEnd = travels.map(t => arrival(t._2))
  val travelDuration = travels.map(t => arrival(t._2) - arrival(t._1))
  val travelLoad = travels.map(t => CPIntVar(sites(t._1).load))
  val travelVehicle = travels.map(t => vehicle(t._1))

  //Transport time for patients:
  val actualTransportTime = travels.map{
    case (stop1, _, true) =>
      val patient = ist.patients(sites(stop1).patient)
      - arrival(stop1) + patient.rdvStart
    case (_, stop2, false) =>
      val patient = ist.patients(sites(stop2).patient)
      departure(stop2) - patient.rdvEnd
  }

  val travelWaitTime = Array.tabulate[CPIntVar](travels.length)(i =>{
    if(actualTransportTime(i).getMax < minTransportTime(i)) CPIntVar(0)
    else CPIntVar(0 to actualTransportTime(i).getMax - minTransportTime(i))
  })


  /* Constraints */

  //Linking service of patients
  for(p <- 0 until nPatient){
    for(i <- sites.indices.filter(sites(_).patient == p)){
      add(patientServiced(p) === stopServiced(i))
    }
  }

  for(t <- travelDuration) add(t >= 0)

  add(inverse(pred, succ))
  add(circuit(pred, symmetric = false), Strong)

  //Vehicle capacity (can be replaced by independent capacity constraints):
  for(v <- 1 until nVehicle)
    add(maxCumulativeResource(travelStart, travelDuration, travelEnd, travelLoad, travelVehicle, CPIntVar(capacities(v)), v))

  // Links the depots
  add(succ(nSite-1) === nStop)
  for (v <- 0 until nVehicle-1) {
    val last = nStop + nVehicle + v
    val first = nStop + v + 1
    add(succ(last) === first)
  }

  for(s <- 0 until nStop) {
    //linking service of stops
    add(stopServiced(s) === (vehicle(s) ?!== 0)) // Real vehicle assigned

    //Linking loads:
    add(load(s) === load(pred(s)) + sites(s).load)

    //Linking departure and arrival times
    add(stopServiced(s) ==> (arrival(s) ?>= departure(pred(s)) + distances(s)(pred(s))))
    add(stopServiced(s) ==> (arrival(succ(s)) ?>= departure(s) + distances(s)(succ(s))))

    add(stopServiced(s) === (duration(s) ?!== 0)) //Service duration set to 0 if not serviced

    // Linking roads
    add(vehicle(pred(s)) === vehicle(s), Strong)
    add(vehicle(succ(s)) === vehicle(s), Strong)
  }

  // Linking travels
  for((t, i) <- travels.zipWithIndex){
    add(vehicle(t._1) === vehicle(t._2))

    //If stop serviced: enforcing that patient arrives on time:
    if(t._3) add(stopServiced(t._2) ==> (arrival(t._2) ?<= sites(t._2).winEnd - sites(t._2).service))

    //If stop not serviced: time set to rdv start or end depending on travel
    val timeIfDummy = if(t._3) sites(t._1).winEnd else sites(t._2).winStart
    add(!stopServiced(t._1) ==> (arrival(t._1) ?=== timeIfDummy))
    add(!stopServiced(t._2) ==> (arrival(t._2) ?=== timeIfDummy))

    //Linking waiting time:
    add(stopServiced(t._1) ==> (travelWaitTime(i) ?=== (actualTransportTime(i) - minTransportTime(i))))
    add(!stopServiced(t._1) ==> (travelWaitTime(i) ?=== 0))
  }


  /* Objective function */

  //Number of serviced stops
  val nServed: CPIntVar = sum(patientServiced) //Total number of patients serviced (to maximize)

  //Waiting time:
  val totalWaitTime: CPIntVar = sum(travelWaitTime) //Total waiting time of patients (to minimize)
//  val maxTravelWaitTime: CPIntVar = maximum(travelWaitTime) //Maximum waiting time among patients (to minimize)

  solver.minimize(-nServed, totalWaitTime)
//  solver.maximize(nServed)


  /* Solution management */

  //sol tracking:
  var currentSol: CPSol = new CPSol(Set[CPIntVar]())

  //On solution:
  onSolution {

    //Printing sol:
    if(!solver.silent) {
//      println("stopServiced: " + stopServiced.mkString(" "))
//      println("successors: " + succ.mkString(" "))
//      println("vehicles: " + vehicle.mkString(" "))
//      println("arrival: " + arrival.mkString(" "))
//      println("departure: " + departure.mkString(" "))
//      println("load: " + load.mkString(" "))

      println("Patients serviced: " + nServed)
      println("Total waiting time: " + Time(totalWaitTime.value))
//      println("Max travel waiting time: " + Time(maxTravelWaitTime.value))

//      travels.indices.filter(t => travelVehicle(t).isBound && travelVehicle(t).value != 0).sortBy(t => travelStart(t).value).foreach(t => {
//        print(if (travels(t)._3) "Forward" else "Backward")
//        print(" travel (id: " + t)
//        print(") for patient " + sites(travels(t)._1).patient)
//        print(" of duration " + travelDuration(t).value)
//        print(" and load " + travelLoad(t).value)
//        print(" is executed on vehicle " + travelVehicle(t).value)
//        print(" at time " + TimeWindow(Time.intToTime(travelStart(t).value), Time.intToTime(travelEnd(t).value)))
//        println(" (rdv was at " + TimeWindow(Time(ist.patients(sites(travels(t)._1).patient).rdvTime), Time(ist.patients(sites(travels(t)._1).patient).rdvEnd)) + ")")
//      })
      println("------------")
    }

    //Checking and saving sol:
    val paths = Array.fill(ist.vehicles.length){ArrayBuffer[Step]()}
    for(i <- sites.indices.filter(i => i < nStop && stopServiced(i).isBound && stopServiced(i).isTrue)) {
      val v = vehicleIndex(vehicle(i).value)
      val operation = if(sites(i).forward) if (sites(i).load >= 0) 0 else 1 else if (sites(i).load >= 0) 2 else 3
      paths(v) += Step(sites(i).place, Time(arrival(i).value).toString(), ist.patients(sites(i).patient).id, operation)
    }
    val sol = Solution(ist, paths.zipWithIndex.map{case (steps, i) => Path(ist.vehicles(i).id, steps.toArray.sortBy(_.time))})

    if(!SolutionChecker.checkSol(sol)) throw new Exception("Invalid solution!")
    JsonParser.writeSol(solPath, sol)

    //Logging objectives:
    log += ((timeElapsed.toDouble/1000000000, solver.objective.objs.map(o => math.abs(o.best)).toArray))

    //Recording sol:
    val boundedVars = mutable.Set[CPIntVar]()
    for(v <- decVars){
      boundedVars += v.selectionVar.asInstanceOf[CPIntVar]
      if(v.selectionVar.isTrue) boundedVars ++= v.optionalVars
    }
    currentSol = new CPSol(boundedVars.toSet)
  }

  def assignSol(sol: Solution): Boolean = {
    var consistent = true
    for(solPath <- sol.paths){
      val vid = solPath.vehicle
      var previous = -1
      var currv = -1
      for(s <- solPath.steps){
        val p = patientPerId(s.patient)
        val i = findStopByStep(s)
        val v = findVehicleByStep(vid, s)

        if(currv != v) previous = -1

        add(patientServiced(p) === 1)
        add(vehicle(i) === v)
        add(arrival(i) === Time(s.time).toMinutes)
        if(previous != -1) add(pred(i) === previous)

        if(!(patientServiced(p).isBound && vehicle(i).isBound && arrival(i).isBound && (previous == -1 || pred(i).isBound))){
          if(!solver.silent) println("Unable to assign step " + s + " of vehicle " + vid)

          consistent = false
        }

        previous = i
        currv = v
      }
    }

    for(pv <- patientServiced){
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


  /* Search */

  //Heuristic sub methods:
  def slackPatientForward(i: Int) = if (ist.patients(i).start >= 0) ist.distMatrix(ist.patients(i).start)(ist.patients(i).destination) else 0
  def slackPatientBackward(i: Int) = if (ist.patients(i).end >= 0) ist.distMatrix(ist.patients(i).destination)(ist.patients(i).end) else 0
  def minConsoPatient(i: Int) = (slackPatientBackward(i) + slackPatientBackward(i)) * ist.patients(i).load
  def vehicleUsage(i: Int) = vehicle.count(v => v.isBoundTo(i))

  //Decision variables:
  val decVars = (for (p <- 0 until nPatient) yield {
    val indices = sites.indices.filter(sites(_).patient == p).toArray

    val decisionVar = patientServiced(p)

    val (pvehicles, parrivals, psucc) = (for(i <- indices) yield (vehicle(i), arrival(i), succ(i))).unzip3
    val ppred = for(i <- indices) yield pred(i)
    val optionalVars = pvehicles ++ parrivals ++ psucc ++ ppred

    val valHeuris = (i: Int) => {
      if(i < pvehicles.length) pvehicles(i).minBy(vehicleUsage)
      else if(i < pvehicles.length + parrivals.length){
        if (optionalVars(i).max <= ist.patients(p).rdvStart) optionalVars(i).max
        else optionalVars(i).min
      }
      else optionalVars(i).randomValue
    }

    val subBranching = conflictOrderingSearch(optionalVars, optionalVars(_).size, valHeuris)

    CPOptionalSelection(decisionVar, optionalVars, subBranching)
  }).toArray

  //Search heuristic:
  val customSearch: Branching = maxSelection(
    decVars,
    conflictOrderingSearch(decVars.map(_.selectionVar), (i) => -minConsoPatient(i), _ => 1)
  )

  //Relaxes randomly relaxSize% of the patients
  val randomPatientRelax = (sol: CPSol, relaxSize: Double) => {
    val nFix = decVars.length - (relaxSize * decVars.length).ceil.toInt

    val varArray = decVars.indices.toArray //map to real indice of variable
    var boundStart = varArray.length //Elements of varArray from this index are bound

    while(decVars.map(_.selectionVar).count(_.isBound) < nFix){
      val i = Random.nextInt(boundStart) //Selecting new decision var to freeze randomly
      val j = varArray(i)

      //Freezing decision var and optional vars
      val b = decVars(j).selectionVar
      val x = decVars(j).optionalVars
      add(b === sol(b))
      if(!b.isBound) throw Inconsistency
      if(b.isTrue) for(opt <- x){
        add(opt === sol(opt))
        if(!opt.isBound) throw Inconsistency
      }

      //marking var as bound:
      boundStart -= 1
      varArray(i) = varArray(boundStart)
      varArray(boundStart) = j
    }
  }

  //LNS:
  def lns(time: Int): Unit = {

    val nBkts = 1000
    val relaxSize = math.min(1.0, 5.0/nPatient)
    val nIters = Int.MaxValue

    val searchEngine = OptionalSelectionLNS(solver, decVars)

    searchEngine.setSol(currentSol)

    //Starting LNS:
    searchEngine.search(randomPatientRelax, customSearch, time * 1000000000L, nIters, relaxSize, nBkts)
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

      search(maxSelection(decVars, binaryFirstFail(decVars.map(_.selectionVar))))
    }

    if (!solver.silent) println(stats)
  }


  /* Execution */

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

  protected case class Stop(
                             patient: Int,
                             place: Int,
                             winStart: Int,
                             winEnd: Int,
                             operation: Int
                           ){
    def isDepot: Boolean = patient == -1

    def category: Int = if(isDepot) -1 else ist.patients(patient).category

    def service: Int = if(isDepot) 0 else ist.patients(patient).srvLen

    def forward: Boolean = operation < 2

    def pickup: Boolean = operation == 0 || operation == 2

    def load: Int = if(isDepot) 0 else if(pickup) ist.patients(patient).load else -ist.patients(patient).load
  }
}