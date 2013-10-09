/* Copyright 2009-2013 EPFL, Lausanne */

package leon.test
package parsing

import leon._

import leon.evaluators._
import leon.utils._

import leon.plugin.{TemporaryInputPhase, ExtractionPhase}

import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Trees._
import leon.purescala.TypeTrees._

class ListParsingTests extends LeonTestSuite {
  private implicit lazy val leonContext = testContext

  private val evaluatorConstructors : List[(LeonContext,Program)=>Evaluator] = List(
    new DefaultEvaluator(_,_),
    new CodeGenEvaluator(_,_)
  )

  private def prepareEvaluators(implicit ctx : LeonContext, prog : Program) : List[Evaluator] = evaluatorConstructors.map(c => c(leonContext, prog))

  //Need to know what is happening for now
  override def generateContext = {
    val reporter = new DefaultReporter(leon.Settings())

    //Remove strict compilation to avoid refreshing the ctx at each test
    LeonContext(
      settings = Settings(strictCompilation=false),
      files = List(),
      reporter = reporter,
      interruptManager = new InterruptManager(reporter)
    )
  }

  private def parseString(str : String) : Program = {
    val pipeline = TemporaryInputPhase andThen ExtractionPhase

    val errorsBefore   = leonContext.reporter.errorCount
    val warningsBefore = leonContext.reporter.warningCount

    val program = pipeline.run(leonContext)((str, Nil))

    assert(leonContext.reporter.errorCount   === errorsBefore)
    assert(leonContext.reporter.warningCount === warningsBefore)

    program
  }

  private def parseFuncTest(testName : String, func : String): Unit = {

    val program = """|object Program {
                     |  import leon.Utils._
                     """ +
                     func +
                     """|}""".stripMargin
    test(testName) {
      try{
        val prog = parseString(program.stripMargin)
      }catch{
        case e : Throwable => 
          //throw new AssertionError("\n"+program.stripMargin+" \n compilation failed.")
          assert(false)
      }
      
    }
  }


  parseFuncTest("Parse SimpleType",
    """|  def typeParse(x : List[Int]) : List[Int] = x""")

  parseFuncTest("Parse ListOfListType",
    """|  def typeParse(x : List[List[Int]]) : List[List[Int]] = x""")

  parseFuncTest("Parse FiniteList",
    """|  def finiteListParse(x : Int) : List[Int] = List[Int](1)""")

  parseFuncTest("Parse Nil",
    """|  def parseNil(): List[Int] = Nil""")

  parseFuncTest("Parse head",
    """|  def parseHead(x : List[Int]): Int = x.head""")

  parseFuncTest("Parse size and length",
    """|  def parseSize(x : List[Int]): Int = x.size
       |  def parseLength(x : List[Int]): Int = x.length
       """)

  parseFuncTest("Parse Tail",
    """|  def parseTail(x : List[Int]): List[Int] = x.tail""")

  parseFuncTest("Parse :::",
    """|  def parseConc(x : List[Int], y : List[Int]) : List[Int] = x ::: y""")

  parseFuncTest("Parse ::",
    """|  def parseAppend(x : List[Int]): List[Int] = 1 :: x """)

  parseFuncTest("Parse apply/at",
    """|  def parseAt(x : List[Int]): Int = x(1)""")

  parseFuncTest("Parse pattern Matching",
    """ | def parsePatMatch(x : List[Int] ): Int = x match {
        | case x::y::Nil =>  x
        | case x::Nil => x
        | case Nil => -1
        |}
    """)
  parseFuncTest("Parse List reverse",
    """ | def reverse(list : List[Int]): List[Int] = list match {
        |   case x :: xs => reverse(xs) ::: (x :: Nil)
        |   case Nil => Nil
        |}""")



}