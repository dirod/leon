package leon
package solvers
package combinators

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.Extractors._


//@TODO: Decide if this should always be used with an underlying FairZ3Solver
/** This solver should be able to prove VC's containing functional list fragments
    Accepted members from the Scala's List specification:
      -Cons
      -length
    Introduced trees for the Extension with Sets of Sublists and Content Sets:
      - greatest common suffix (gcs), ListxList->List
      - isSublist predicate, ListxList->Bool
      - Pre

    Note that we assume that the VC always requires the Sets of Sublists and Content Sets
    extension.
  * @param underlying The underlying solver
*/
class FLSSolver[+S <: Solver](underlying: S) extends RewritingSolver[S, Map[Expr,Expr]](underlying) with TimeoutSolver{
  import FLS2CompletionAxioms._
  
  def name = "FLS Solver"

  val reporter = context.reporter

  def debugMess(title : String, content : String): Unit = {
    val largebar = "="*40
    val smallbar = "-"*40
    reporter.debug(largebar)
    reporter.debug(title)
    reporter.debug(smallbar)
    reporter.debug(content)
    reporter.debug(largebar)
  }

  def debugMess(title : String, content : Set[Expr], sep: String = "\n"): Unit = {
    debugMess(title, content.mkString(sep))
  }

  var origParamIDs: Set[Identifier] = Set()
  


  type SublistSetID = Identifier
  //This contains the maping between a list variable and it's set of subLists
  private var sigmaMap : Map[Expr,SublistSetID] = Map()
  private var count = 0
  private var revSigmaMap : Map[SublistSetID, Expr] = Map()

  private def sublistSetVar(v : Expr): SublistSetID = sigmaMap.get(v) match {
    case Some(v) => v
    case None => {
      val freshID = FreshIdentifier("S"+count, true).setType(SetType(v.getType))
      count += 1
      sigmaMap += (v->freshID)
      freshID
    }
  } 

  /** This should remove every x = Cons(y, ys) from this expr, 
      and replace them with x.head = y && x.tail = ys && x != Nil
   *
   * @param expression The negated VC 
   * @return An expression without Cons constructs
   */
  private def elimCons(expr: Expr): Expr = {
    //Assuming there is no Cons yet
    expr
  }

  /** This returns the set of ground subterms of the clause
      @param clause The clause
      @return the set of ground subterms
  */
  private def groundSubtermsOf(clause : Expr): Set[Expr] = {
    def groundSubtermsOf0(term : Expr, acc : Set[Expr] = Set()): Set[Expr] = term match {
      //These cases are ground Subterms
      case v @ Variable(id) if(v.getType.isInstanceOf[ListType]) => acc + v
      case Cdr(list) => groundSubtermsOf0(list, acc + term)
      case Car(list) => groundSubtermsOf0(list, acc)
      case ListLength(list) => groundSubtermsOf0(list, acc)
      case UnaryOperator(t, _) => groundSubtermsOf0(t, acc)
      case BinaryOperator(l, r, _) => 
        groundSubtermsOf0(l,acc) ++ groundSubtermsOf0(r, acc)
      case NAryOperator(seq, _) => 
        seq.map(groundSubtermsOf0(_, acc)).toSet.flatten
      case term : Terminal => Set()
      //Called after elimCons, there shouldn't be any Cons here
      //case t @ Cons(head, tail) => groundSubterms()
      case _ => sys.error("Error matching groundSubtermsOf0 with :"+term)
    }

    //If this doesn't pass, this is not a clause.
    clause match {
      case Or(seq) => seq.map(groundSubtermsOf0(_)).toSet.flatten
      case t => groundSubtermsOf0(t)
    }
  }
  //Closes substerms, therefore axiom instantiation terminates
  private def extendedGroundSubterms(sts : Set[Expr]): Set[Expr] = {
    def crossSelf2(s : Set[Expr]): Set[(Expr, Expr)] = {
      (for(e0 <- s; e1 <- s if(e0 != e1)) yield (e0, e1))
    }

    def psy0(sts : Set[Expr]): Set[Expr] = {
      val pairs = crossSelf2(sts)
      sts ++ pairs.map(p => Gcs(p._1,p._2))
    }

    def psy(psy0 : Set[Expr]): Set[Expr] = {
      //Heads cannot be instantiated in any axiom
      //val heads = psy0.map(Car(_))
      val pairs = crossSelf2(psy0)
      val pretails = pairs.map(p => Set(Pre(p._1, p._2), Cdr(Pre(p._1, p._2)))).flatten
      psy0 ++ pretails
    }

    psy(psy0(sts))
  }

  /** This should return the set of ground clauses of a given expression

  * @param expression The expression after elimcons
  * @return A set of ground clauses
  */

  private def groundClauses(expression: Expr): Set[Expr] = {
    //For now, it generates the CNF of expression
    //This is the nnf
    def pre(expr : Expr): Expr = expr match {
      case Not(Not(e)) => pre(e)
      case Not(And(seq)) => Or(seq.map(p => pre(Not(p))))
      case Not(Or(seq)) => And(seq.map(p => pre(Not(p))))
      case And(seq) => And(seq.map(p => pre(p)))
      case Or(seq) => Or(seq.map(p => pre(p)))
      case Not(e) => Not(pre(e))
      case _ => expr
    }
  
    
    toCNF(simplePreTransform(pre)(expression)) match {
      case And(seq) => seq.toSet
      case clause => Set(clause)
    }
  }



  /** This should remove length functions
      For each x : list variable in expression :
        - Add X = sigma(x) the set of all sublists (suffixes) of x
        - Add variable x_length = |X| - 1 
        - Replace each x.length by x_length
  *
  * @param expression the VC (not negated please :))
  * @return the VC without any List.length function (and with a bunch of other definitions)
  */
  private def removeLengthFunction(expression : Expr) : Expr = {

    sys.error("TODO")
  }

  private def aliasSublistSets(setCnstrs : Set[Expr]): Set[Expr] = {

    //Pre transform
    def aliasSigma(cnstr : Expr): Expr = cnstr match {
      case Sigma(e) => Variable(sublistSetVar(e))
      case _ => cnstr
    }

    //Post transform
    def aliasHeadsTails(cnstr : Expr): Expr = cnstr match {
      case Car(list) => HeadFLS(Variable(sublistSetVar(list)))
      case _ => cnstr
    }

    //This should always work after generateSetConstraints
  

    val aliased = setCnstrs.map(simpleTransform(aliasSigma, aliasHeadsTails)(_))
    aliased

  }

  private def simpleToBapaConversions(e : Expr): Expr = {
    def c0(e : Expr): Expr = e match {

       case Equals(list, nil @ NilList(_)) => Equals(SetCardinality(Sigma(list)), IntLiteral(1))
       case Equals(nil @ NilList(_), list) => Equals(SetCardinality(Sigma(list)), IntLiteral(1))
       case Equals(list1, list2) if(list1.getType.isInstanceOf[ListType]) => Equals(Sigma(list1), Sigma(list2))
       case IsSubList(list1, list2) => 
         SubsetOf(Sigma(list1), Sigma(list2))
       case ListLength(list) => Minus(SetCardinality(Sigma(list)), IntLiteral(1))
       case Gcs(list1,list2) => SetIntersection(list1, list2)//.setType(SetType(list1.getType))
       case Not(e) => Not(c0(e))
       case Or(seq) => Or(seq.map(c0).filter(_ != BooleanLiteral(true)))

       //There shouldn't be any && here, e should be a clause !
       case _ => e
    }
    simplePreTransform(c0)(e)
  }


  def rewriteCnstr(expression : Expr) : (Expr,Map[Expr,Expr]) = {
    origParamIDs = variablesOf(expression).toSet
    //Assumes that lets can be simplified
    val simplifiedLets = expression

    debugMess("Received as input : ", simplifiedLets.toString)
    
    val clauses : Set[Expr] = groundClauses(elimCons(simplifiedLets))
    
    debugMess("Clauses : ", clauses)

    val sts : Set[Expr] = groundSubtermsOf(expression)
    val exSubTerms : Set[Expr] = extendedGroundSubterms(sts)
    debugMess("Extended set of ground terms ("+exSubTerms.size+") : ", exSubTerms)

    
    val instantiator = new AxiomsInstantiation(exSubTerms, KPre)
   
    val instances = instantiator.instantiateAxioms

    // debugMess("Instantiated Axioms : ", instances)

    // val instancesAndClauses = instances++clauses

    // debugMess("Axioms instantiation and clauses : ", instancesAndClauses)

    // val rewCnstr = groundClauses(And(instancesAndClauses.toSeq))

    // debugMess("PRP structure: ", rewCnstr)
    val prpStruct = new PRPStruct(instances, clauses)
    val bapaPrPStruct = simpleToBapaConversions(And(prpStruct.prpstruct.toSeq))

    val setCnstrs = prpStruct.sublistCnstr.toSet + bapaPrPStruct

    debugMess("Set Constraints : ", setCnstrs)

    val aliased = aliasSublistSets(setCnstrs)
    val title = "Aliased Constraints : \nWhere :\n"+sigmaMap.mkString("\n")
    debugMess(title, aliased)

    val listOfSigmas = sigmaMap.toList.unzip._2

    val sizeCnstrs : List[Expr] = listOfSigmas.map( p => {
      val SetType(ListType(base)) = p.getType
      val nil = NilList(base)
      val s = sigmaMap(nil)
      //SubsetOf(Variable(s), Variable(p))
      GreaterThan(SetCardinality(Variable(p)), IntLiteral(0))
      })

    debugMess("Added size constraints :  ", sizeCnstrs.toSet)


    val sentToZ3 = /*sizeCnstrs.toSeq ++*/ aliased.toSeq

    debugMess("SentToZ3 : ", sentToZ3.mkString("\n"))


    (And(sentToZ3), Map())
  }


  class NoModelTranslation(t: Expr) extends Exception("Can't translate back from sublistset model" + t)

  def reconstructModel(model : Map[Identifier,Expr], meta : Map[Expr,Expr]) : Map[Identifier,Expr] = {
    println("Reconstruct Model")
    def toListModel(expr : Expr): Expr = expr match {
      //The emptySet
      case FiniteSet(Seq()) =>
        val tpe = expr.getType
        NilList(tpe)
      case _ => throw new NoModelTranslation(expr)
    }

    debugMess("Returned model", model.mkString("\n"))
    model.filter(p => origParamIDs(p._1))

  }

  //TimeoutSolver things

  def interrupt(): Unit = {
    Unit
  }

  def recoverInterrupt(): Unit = {
    Unit
  }

  protected def innerCheck: Option[Boolean] = {
    underlying.check
  }

  /**
  This class represents a PRP structure
  */
  class PRPStruct(val axiomsInstances : Set[Expr], val vc : Set[Expr]){
    val prpstruct = groundClauses(And(axiomsInstances.toSeq ++ vc.toSeq))
    private val alphaList: Set[Expr] = alphaListSet
    private var Segs: Set[Sxy] = Set()
    val sublistCnstr = generateSetConstraints
    val contentCnstr = generateSetContentConstraints
    //This defines S(x,y) where x and y are bound by the isSublist_1 relation
    type Sxy = (Expr, Expr)
    type TailDefd = (Expr, Expr)
    /**
      This returns the set of terms of type list in the clauses
    */
    private def alphaListSet: Set[Expr] = {
      def alphaListSet0(term : Expr, acc : Set[Expr] = Set()): Set[Expr] = term match {
        //These cases are ground Subterms
        case v @ Variable(id) if(v.getType.isInstanceOf[ListType]) => acc + v
        case Cdr(l) => alphaListSet0(l, acc + term)
        case Gcs(l ,r) => alphaListSet0(l, acc + term) ++ alphaListSet0(r, acc + term)
        case UnaryOperator(t, _) => alphaListSet0(t, acc)
        case BinaryOperator(l, r, _) => 
          alphaListSet0(l,acc) ++ alphaListSet0(r, acc)
        case NAryOperator(seq, _) => 
          seq.map(alphaListSet0(_, acc)).toSet.flatten
        case term : Terminal => Set()
        //Called after elimCons, there shouldn't be any Cons here
        //case t @ Cons(head, tail) => groundSubterms()

        case _ => sys.error("Error matching alphaListSet with :"+term)
      }

      prpstruct.map(alphaListSet0(_)).flatten  
    }

    private def segToSetDiff(segxy : Sxy): Expr = {
      val (x,y) = segxy
      val sigmaY = Sigma(y)
      val setY = FiniteSet(Seq(y)).setType(sigmaY.getType)

      val innerDiff = SetDifference(sigmaY, Sigma(x)).setType(sigmaY.getType)
      val outerDiff = SetDifference(innerDiff, setY).setType(sigmaY.getType)
      outerDiff
    }

    private def crossSelf2(s : Set[Expr]): Set[(Expr, Expr)] = {
      (for(e0 <- s; e1 <- s if(e0 != e1)) yield Set((e0, e1), (e1, e0))).flatten
    }

    def clauseContains(p : Expr => Boolean): Boolean = {
      def clauseContains0(expr: Expr, p : Expr => Boolean): Boolean = {
        if(p(expr))
          true
        else expr match {
          case UnaryOperator(t, _) => clauseContains0(t, p)
          case BinaryOperator(l, r, _) =>
            clauseContains0(l, p) || clauseContains0(r, p)
          case NAryOperator(seq, _) =>
            seq.exists(e => clauseContains0(e, p))
          case term : Terminal => p(expr)
          case _ => sys.error("Error matching clauseContains0 with :"+expr)
        }
      }

      prpstruct.exists(e => clauseContains0(e, p))
    }

    def clauseFind(p : Expr => Option[Expr]): Option[Expr] = {
      def clauseFind0(expr : Expr, p : Expr => Option[Expr]): Option[Expr] = {
        val e = p(expr)
        if(e != None)
          e
        else expr match {
          case UnaryOperator(t,_) => clauseFind0(t, p)
          case BinaryOperator(l, r, _) => clauseFind0(l, p) match {
            case None => clauseFind0(r,p)
            case r @ _ => r
          }
          case NAryOperator(seq, _) =>
            seq.find(e => p(e).isDefined)
          case term : Terminal => p(expr)
          case _ => sys.error("Error matching clauseContains0 with :"+expr)
        }
      }
      prpstruct.find(e => clauseFind0(e, p).isDefined) 
    }

    //These predicates will be used to define the sublist_1 relation and the defined tails
    private def isSublist(expr : Expr, pair : (Expr, Expr)): Boolean = {
      val (x, y) = pair
      expr match {
        case IsSubList(lhs, rhs) if(lhs == x && rhs == y) => true
        case _ => false
      }
    }
    private def notEqual(expr : Expr, pair : (Expr, Expr)): Boolean = {
      val (x, y) = pair
      expr match {
        case Not(Equals(lhs, rhs)) =>
          ((lhs == x) && (rhs == y))
        case _ => false 
      }
    }

    //This returns x if there is an x s.t tail(y) == x
    private def isTailUndefined(expr : Expr, x : Expr, y: Expr): Option[Expr] = expr match {
      case Equals(lhs, rhs) => 
        val taily = Cdr(y).setType(y.getType)
        if(lhs == taily && rhs == x)
          Some(x)
        else if(rhs == taily && lhs == x)
          Some(x)
        else
          None
      case _ => None
    }

    //This defines the forth condition for the sublist_1 relation
    //Very heavy function
    private def thereIsNoMiddle(pair : (Expr, Expr)): Boolean = {
      val (x, y) = pair
      ! alphaList.exists(z => 
        (x != y && x != z && y != z) &&
        (clauseContains(e => isSublist(e, (x,z))) && 
        clauseContains(e => isSublist(e, (z,y)))))
    } 

    private def generateSetConstraints: Seq[Expr] = {
      val types = alphaList.map(_.getType match {case ListType(inner) => { Some(inner)}; case _ => None}).filter(p => p != None).map(_.get)

      //Generate Sigma(nil) = {nil} for each list type
      val sigmaNils = types.map{ tpe =>
        val nil = NilList(tpe)
        val sigma = Sigma(nil)
        val set = FiniteSet(nil :: Nil).setType(sigma.getType)
        Equals(sigma, set)
      }

      val alphaListPairs = crossSelf2(alphaList)

      val step3Cnstrs = for(y <- alphaList) yield {
        var definedy : Seq[Expr] = Seq()
        var segsy : Seq[Expr] = Seq()
        val sigmaY = Sigma(y)
        
        val tpe @ ListType(inner) = y.getType
        val setY : Expr = FiniteSet(Seq(y))
        for(x <- alphaList if(x != y)) yield {

          clauseFind(p => isTailUndefined(p, x, y)) match {
            //Case 2: there is x s.t. x = tail(y)
            case Some(x) => 
              definedy = definedy :+ Sigma(x) 
            //Case 3: There may be a Sxy between x and y if x isSublist of y && there is no z
            case None => if(clauseContains(p => isSublist(p, (x,y))) && thereIsNoMiddle(x,y)) {
              val sxy = (x,y)
              Segs = Segs + sxy
              segsy = segsy :+ segToSetDiff(sxy)
            }
          }
        }
        //Constructs sigma(y) = {y} U ...
        val union = (segsy ++ definedy).foldLeft(setY)((l,r) => SetUnion(l,r).setType(sigmaY.getType))
        Equals(sigmaY, union)
      }

      /*Existentially quantify over segs, create set disjunctions of point 3.4 and then replace
        with equivalent expression of set differences
      */
      val step4Cnstrs = for(x <- alphaList; sxy <- Segs) yield{
        val setX = FiniteSet(Seq(x)).setType(SetType(x.getType))
        val sigmaxydiff = segToSetDiff(sxy)
        val conj = SetIntersection(sigmaxydiff, setX).setType(setX.getType)
        Equals(SetCardinality(conj), IntLiteral(0))
      }


      sigmaNils.toSeq ++ step3Cnstrs.toSeq ++ step4Cnstrs.toSeq 
    }

  /** This applies the procedure described in p.14.
  */
  private def generateSetContentConstraints : Seq[Expr] = {
    Seq()
  }
  }



  class AxiomsInstantiation(sts : Set[Expr], axioms : Set[Axiom]) {

    lazy val cross2 = crossSelf2(sts)
    lazy val cross3 = crossSelf3(sts)

    /** For a given FLS formula. Return all the possible axiom instantiations
      @param expression : A FLS formula
      @return the set of instantiated axioms
    */
    def instantiateAxioms : Set[Expr] = {
      axioms.map(instantiateAxiom(_)).flatten
    }

    /**This instantiates the axioms.
      @param the verification conditions
      @return  an Axiom
    */
    private def instantiateAxiom(axiom : Axiom): Set[Expr] = {
      axiom match {
        case axiom : UnaryAxiom =>
          debugMess("Instantiating axiom with "+sts.size+": ", axiom.toString)
          sts.map(axiom(_))
        case axiom : BinaryAxiom =>
          debugMess("Instantiating axiom with "+cross2.size+": ", axiom.toString)
          cross2.map(axiom(_))
          Set()
        case axiom : TernaryAxiom =>
          debugMess("Instantiating axiom with "+cross3.size+": ", axiom.toString)
          cross3.map(axiom(_))
  
      }
    }
    def crossSelf2(s : Set[Expr]): Set[(Expr, Expr)] = {
        (for(e0 <- s; e1 <- s if(e0 != e1)) yield Set((e0, e1), (e1, e0))).flatten
    }
    def crossSelf3(s : Set[Expr]): Set[(Expr, Expr, Expr)] = {
        (for(p <- cross2; e2 <- s if(p._1 != e2 && p._2 != e2)) yield {
          val e0 = p._1
          val e1 = p._2
          Set((e0, e1, e2), (e0, e2, e1),
              (e1, e0, e2), (e1, e2, e0), 
              (e2, e0, e1), (e2, e1, e0))
        }).flatten
    }
  }
  /**
    These objects instantiate axioms. They must be fed with ground terms of list type
  */
  object FLS2CompletionAxioms {
    /* Notes about the local theory extension
    Omega_e = {head, tail, gcd}
    Sigma_0 = {S_FLS, {nil, isSublist}}
    S_FLS = {bool, list data}
    K_FLSf = {Pure, NoCycle{1,2}, Refl, Trans, AntiSym, Total, UnfoldL, UnfoldR, GCS{1,2,3}}
    T_0 = {NoCycle1, Refl, Trans, AntiSym, Total}
    K_e = K_FLSf \ T_0
    */
    lazy val K_FLSf : Set[Axiom] = Set(Pure, NoCycle1, NoCycle2, Refl, Trans, AntiSym,
                                       Total, UnfoldL, UnfoldR, GCS1, GCS2, GCS3)
    lazy val T_0 : Set[Axiom] = Set(NoCycle1, Refl, Trans, AntiSym, Total)
    lazy val K_e : Set[Axiom] = (K_FLSf -- T_0)
    //This is the set of axioms that will give a PRP struct for FLS^2
    lazy val KPre = K_e + PreA


    trait Axiom {
      def arity : Int
      def apply(sts : Seq[Expr]): Option[Expr]
    }

    trait UnaryAxiom extends Axiom {
      def arity = 1
      def apply(sts : Seq[Expr]): Option[Expr] = sts match{
        case st :: Nil => Some(this(st))
        case _ => None
      }
      def apply(st : Expr): Expr
    }

    trait BinaryAxiom extends Axiom {
      def arity = 2
      def apply(sts : Seq[Expr]): Option[Expr] = sts match {
        case st0 :: st1 :: Nil => Some(this(st0,st1))
        case _ => None
      }

      def apply(sts : (Expr, Expr)): Expr = sts match {
        case (st0, st1) => this(st0, st1)
      }

      def apply(st0 : Expr, st1 : Expr): Expr
    }

    trait TernaryAxiom extends Axiom {
      def arity = 3
      def apply(sts : Seq[Expr]): Option[Expr] = sts match {
        case st0 :: st1 :: st2 :: Nil => Some(this(st0, st1, st2))
        case _ => None
      }

      def apply(sts: (Expr, Expr, Expr)): Expr = sts match {
        case (st0, st1, st2) => this(st0, st1, st2)
      }

      def apply(st0 : Expr, st1 : Expr, st2 : Expr): Expr
    }

    object PreA extends BinaryAxiom {
      def apply(x : Expr, y : Expr): Expr = {
        val tpe @ ListType(inner) = x.getType
        val pre = Pre(x,y)
        val gcs = Gcs(x,y)
        val lhs0 = Not(Equals(x,y))
        val lhs1 = Not(Equals(x, gcs))
        val lhs2 = Not(Equals(y, gcs))
        val rhs0 = IsSubList(pre, x)
        val rhs1 = Equals(Cdr(pre), gcs)
        val lhs = And(Seq(lhs0, lhs1, lhs2))
        val rhs = And(Seq(rhs0, rhs1))
        Or(Not(lhs), rhs)
      }
    }

    object Pure extends BinaryAxiom {
      def apply(x : Expr, y : Expr): Expr = {
          val tpe @ ListType(inner) = x.getType
          val heads = Equals(Car(x).setType(inner), Car(y).setType(inner))
          val tails = Equals(Cdr(x).setType(tpe), Cdr(y).setType(tpe))

          val nilList = NilList(inner)
          val rhs = Or(Seq(Equals(x,y),Equals(x,nilList), Equals(y, nilList)))
          val lhs = And(Seq(heads, tails))
          Or(Not(lhs), rhs)
          //Implies(lhs, rhs)
      }
    }

    object NoCycle1 extends UnaryAxiom {
      def apply(x : Expr): Expr = {
        val ListType(inner) = x.getType
        val nilList = NilList(inner)
        IsSubList(nilList, x)
      }
    }

    object NoCycle2 extends UnaryAxiom {
      def apply(x : Expr): Expr = {
        val tpe @ ListType(inner) = x.getType
        val nilList = NilList(inner)
        val lhs = Equals(Cdr(x).setType(tpe), x)
        val rhs = Equals(x, nilList)
        Or(Not(lhs), rhs)
        //Implies(lhs, rhs)
      }
    }

    object Refl extends UnaryAxiom {
      def apply(x : Expr): Expr = {
        IsSubList(x,x)
      }
    }

    object Trans extends TernaryAxiom {
      def apply(x : Expr, y : Expr, z : Expr): Expr = {
        val lhs = And(Seq(IsSubList(x,y), IsSubList(y,z)))
        val rhs = IsSubList(x,z)
        Or(Not(lhs), rhs)
        //Implies(lhs, rhs)
      }
    }

    object AntiSym extends BinaryAxiom {
      def apply(x : Expr, y : Expr): Expr = {
        val lhs = And(Seq(IsSubList(x,y), IsSubList(y,x)))
        val rhs = Equals(x,y)
        Or(Not(lhs), rhs)
        //Implies(x,y)
      }
    }

    object Total extends TernaryAxiom {
      def apply(x : Expr, y : Expr, z : Expr): Expr = {
        val lhs = And(Seq(IsSubList(y,x), IsSubList(z,x)))
        val rhs = Or(Seq(IsSubList(y,z), IsSubList(z,y)))
        Or(Not(lhs), rhs)
        //Implies(lhs, rhs)
      }
    }

    object UnfoldL extends UnaryAxiom {
      def apply(x : Expr): Expr = {
        val tpe @ ListType(inner) = x.getType
        val lhs = Cdr(x).setType(tpe)
        IsSubList(lhs, x)
      }
    }

    object UnfoldR extends BinaryAxiom {
      def apply(x : Expr, y : Expr): Expr = {
          val tpe @ ListType(inner) = x.getType
          val lhs = IsSubList(x,y)
          val rhs = Or(Seq(Equals(x,y), IsSubList(x, Cdr(y).setType(tpe))))
          Or(Not(lhs), rhs)
          //Implies(lhs, rhs)
      }
    }

    object GCS1 extends BinaryAxiom {
      def apply(x : Expr, y : Expr): Expr = {
        IsSubList(Gcs(x,y), y)
      }
    }

    object GCS2 extends BinaryAxiom {
      def apply(x : Expr, y : Expr): Expr = {
        IsSubList(Gcs(x,y), x)
      }
    }

    object GCS3 extends TernaryAxiom {
      def apply(x : Expr, y : Expr, z : Expr): Expr = {
        val lhs = And(Seq(IsSubList(z,x), IsSubList(z, y)))
        val rhs = IsSubList(z, Gcs(x,y))
        Or(Not(lhs), rhs)
        //Implies(lhs, rhs)
      }
    }

  }

}