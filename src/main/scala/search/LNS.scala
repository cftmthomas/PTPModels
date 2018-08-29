package search

import oscar.algo.Inconsistency
import oscar.algo.search.{Branching, DFSearch}
import oscar.cp._
import oscar.cp.core.variables.CPIntVar
import oscar.cp.core.{CPSol, CPSolver}

import scala.collection.mutable

abstract class LNSTemplate(solver: CPSolver) {
  var startTime: Long = System.nanoTime()
  var endTime: Long = Long.MaxValue
  var currentSol: CPSol = new CPSol(Set())
  var nIters: Int = Int.MaxValue
  var nBkts: Int = Int.MaxValue

  def recordSol(): Unit

  solver.onSolution{
    recordSol()
  }

  val stopCondition: (DFSearch) => Boolean = (s: DFSearch) => {
    var stop = s.nBacktracks >= nBkts
    stop |= now >= endTime
    stop
  }

  def setSol(sol: CPSol): Unit = {
    currentSol = sol
  }

  def search(
              relaxHeuristic: (CPSol, Double) => Unit,
              searchHeuristic: Branching,
              availTime: Long = 30000000000L,
              nIterations: Int = Int.MaxValue,
              relaxS: Double = 0.5,
              nBacktracks: Int = 500
            ): Unit = {
    startTime = now
    endTime = startTime + availTime
    nIters = nIterations
    nBkts = nBacktracks
    var relaxSize = relaxS

    solver.search(searchHeuristic)

    if(currentSol.dict.isEmpty){
//      println((availTime/1000000L).toInt)
      val stats = solver.start(nSols = 1, failureLimit = Int.MaxValue, timeLimit = (availTime / 1000000L).toInt, maxDiscrepancy = Int.MaxValue)
      if(!solver.silent) println(stats)
    }

    var iter = 0
    var nCompleted = 0
    var nNotCompleted = 0
    var nSolFound = 0
    val stagnationTreshold = 20
    var stop = false
    while (now < endTime && iter < nIters && !stop) {
      if(!solver.silent) println("Starting new LNS Iter(Remaining time: " + (remainingTime/1000000000) + "s, relaxSize: " + relaxSize*100 + "%, nBacktracks: " + nBkts + ")")
      try{
        val stats = solver.startSubjectTo(stopCondition, Int.MaxValue, null) {
          relaxHeuristic(currentSol, relaxSize)
        }
        if(stats.nSols > 0){
          nSolFound = 0
        }else{
          nSolFound += 1
          if(nSolFound >= stagnationTreshold * 10){
            nSolFound = 0
            relaxSize = math.min(1.0, relaxSize * 1.2)
          }
        }
        if(stats.completed){
          nNotCompleted = 0
          if(relaxSize >= 1.0) stop = true
          else if(nCompleted+1 >= stagnationTreshold){
            relaxSize = math.min(1.0, relaxSize * 1.2)
            nCompleted = 0
          }
          else nCompleted += 1
        }
        else{
          nCompleted = 0
          if(nNotCompleted+1 >= stagnationTreshold){
            nBkts = math.min(50000, (nBkts * 1.2).toInt)
            nNotCompleted = 0
          }
          else nNotCompleted += 1
        }
        if(!solver.silent) println(stats)
      }
      catch {
        case _: Inconsistency => if(!solver.silent) println("Search space empty")
      }
      iter += 1
    }
  }

  def searchFrom(
                  sol: CPSol,
                  relaxHeuristic: (CPSol, Double) => Unit,
                  searchHeuristic: Branching,
                  availTime: Long = 30000000000L,
                  nIterations: Int = Int.MaxValue,
                  relaxSize: Double = 0.5,
                  nBacktracks: Int = 500
                ): Unit = {

    currentSol = sol

    search(relaxHeuristic, searchHeuristic, availTime, nIterations, relaxSize, nBacktracks)
  }

  def getSol: CPSol = currentSol

  def now: Long = System.nanoTime()

  def elapsedTime: Long = now - startTime

  def remainingTime: Long = endTime - now

}

class BasicLNS(solver: CPSolver, vars: Array[CPIntVar]) extends LNSTemplate(solver){
  override def recordSol(): Unit = currentSol = new CPSol(vars.toSet)
}

class OptionalSelectionLNS(solver: CPSolver, vars: Array[CPOptionalSelection]) extends LNSTemplate(solver){
  override def recordSol(): Unit = {
    val boundedVars = mutable.Set[CPIntVar]()

    for(v <- vars){
      boundedVars += v.selectionVar.asInstanceOf[CPIntVar]
      if(v.selectionVar.isTrue) boundedVars ++= v.optionalVars
    }

    currentSol = new CPSol(boundedVars.toSet)
  }
}

object BasicLNS{
  def apply(solver: CPSolver, vars: Array[CPIntVar]) = new BasicLNS(solver, vars)
}

object OptionalSelectionLNS{
  def apply(solver: CPSolver, vars: Array[CPOptionalSelection]) = new OptionalSelectionLNS(solver, vars)
}
