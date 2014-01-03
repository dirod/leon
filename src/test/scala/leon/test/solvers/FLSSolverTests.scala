package leon.test
package solvers

import leon.utils._
import leon._
import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Trees._
import leon.purescala.TreeOps._
import leon.purescala.TypeTrees._

import leon.solvers._
import leon.solvers.z3._
import leon.solvers.combinators.FLSSolver

class FLSSolverTests extends LeonTestSuite {
  override def generateContext = {
    var settings  = Settings()
    val debugSections = Set(DebugSectionSolver)
    settings = settings.copy(debugSections = debugSections.toSet)
    val reporter = new DefaultReporter(settings)

    LeonContext(
      settings = settings,
      files = List(),
      reporter = reporter,
      interruptManager = new InterruptManager(reporter)
    )
  }


  private val minimalProgram = Program(
       FreshIdentifier("Minimal"), 
          ObjectDef(FreshIdentifier("Minimal"), Seq(
              fDef
          ), Seq.empty)
      )
  private val fx   : Identifier = FreshIdentifier("x").setType(Int32Type)
  private val fDef : FunDef = new FunDef(FreshIdentifier("f"), Int32Type, VarDecl(fx, Int32Type) :: Nil)
  fDef.body = Some(Plus(Variable(fx), IntLiteral(1)))
  private val solver = SimpleSolverAPI(SolverFactory(() => new FLSSolver(new FairZ3Solver(testContext, minimalProgram))))
  private var testCounter : Int = 0
  private def solverCheck(solver : SimpleSolverAPI, expr : Expr, expected : Option[Boolean], msg : String) = {
    testCounter += 1

    test("Solver test #" + testCounter) {
      assert(solver.solveVALID(expr) === expected, msg)
    }
  }

  val lX = FreshIdentifier("lx").setType(ListType(Int32Type))
  val lY = FreshIdentifier("ly").setType(ListType(Int32Type))
  val listX = Variable(lX)
  val listY = Variable(lY)

  private def assertValid(solver : SimpleSolverAPI, expr : Expr) = solverCheck(
    solver, expr, Some(true),
    "Solver should prove the formula " + expr + " valid."
  )

  private def assertInvalid(solver : SimpleSolverAPI, expr : Expr) = solverCheck(
    solver, expr, Some(false),
    "Solver should prove the formula " + expr + " invalid."
  )

  private def assertUnknown(solver : SimpleSolverAPI, expr : Expr) = solverCheck(
    solver, expr, None,
    "Solver should not be able to decide the formula " + expr + "."
  )

  private def length(e : Expr): Expr = ListLength(e)
  private def lt(e : Expr, i : Expr) = LessThan(e, i)
  private def nil = NilList(Int32Type)
  private def issl(x : Expr, y : Expr) = IsSubList(x, y)
  private def tail(e : Expr) = Cdr(e).setType(e.getType)


  assertInvalid(solver, lt(length(listX), IntLiteral(0)))
  assertValid(solver, issl(listX, tail(listX)))

}