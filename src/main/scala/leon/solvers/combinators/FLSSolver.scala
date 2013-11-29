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
    Introducted trees for the Extension with Sets of Sublists and Content Sets:
      - greatest common suffix (gcs), ListxList->List
      - isSublist predicate, ListxList->Bool

    Note that we assume that the VC always requires the Sets of Sublists and Content Sets
    extension. Therefore the decision procedure for theory FLS (described in Section 6) will
    not be used. Therefore, we always go through a PRP structure.
  * @param underlying The underlying solver
*/
class FLSSolver[+S <: Solver](underlying: S) extends RewritingSolver[S, Map[Expr,Expr]](underlying){
  import FLS2CompletionAxioms._
  
  def name = "FLS Solver"

  type SublistSetVariable = Variable
  //This contains the maping between a list variable and it's set of subLists
  private var sigmaMap : Map[Variable,SublistSetVariable] = Map()

  private def toSetOfSubLists(v : Variable): Option[SublistSetVariable] = sigmaMap.get(v)

  private def defNewSublistSetVar(v : Variable): SublistSetVariable = sigmaMap.get(v) match {
    case Some(v) => v
    case None => {
      val freshID = FreshIdentifier(v.id.name.toUpperCase, true).setType(SetType(v.getType))
      val freshVariable = Variable(freshID)
      sigmaMap += (v->freshVariable)
      freshVariable
    }
  } 

  /** This should remove every x = Cons(y, ys) from this expr, 
      and replace them with x.head = y && x.tail = ys && x != Nil
   *
   * @param expression The negated VC 
   * @return An expression without Cons constructs
   */
  private def elimCons(expression: Expr): Expr = {
    //Assuming there is no Cons yet
    expression
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
      case Car(list) => groundSubtermsOf0(list, acc + term)
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

  /** This may be useful if it is possible
    @param alpha the structure that may be PRP
    @return true iff alpha is a prp structure
  */
  private def isPRPStructure(alpha: Expr) : Boolean = {
    sys.error("TODO")
  }

  /** For a given FLS formula. Return all the possible axiom instantiations
    @param expression : A FLS formula
    @return the set of instantiated axioms
  */
  private def instantiateAxioms(expression : Expr): Set[Expr] = {
    //For now the ground terms can only be variables
    val groundSubTerms : Set[Expr] = groundSubtermsOf(expression)
    K_e.map(instantiateAxiom(groundSubTerms,_)).flatten
  }

  private def instantiateAxiom(sts : Set[Expr], axiom : Axiom): Set[Expr] = {
    def crossSelf2(s : Set[Expr]): Set[(Expr, Expr)] = {
      (for(e0 <- s; e1 <- s if(e0 != e1)) yield Set((e0, e1), (e1, e0))).flatten
    }
    def crossSelf3(s : Set[Expr]): Set[(Expr, Expr, Expr)] = {
      (for(e0 <- s; e1 <- s; e2 <-s if(e0 != e1 && e1 != e2 && e2 != e0)) yield 
        Set((e0, e1, e2), (e0, e2, e1),
            (e1, e0, e2), (e1, e2, e0), 
            (e2, e0, e1), (e2, e1, e0))).flatten
    }

    axiom match {
      case axiom : UnaryAxiom => 
        sts.map(axiom(_))
      case axiom : BinaryAxiom =>
        crossSelf2(sts).map(axiom(_))
      case axiom : TernaryAxiom =>
        crossSelf3(sts).map(axiom(_))
    }
  }
  /** This applies the procedure described in p.14.
    @param prpStruct : The derived PRP structure
    @return the set constraint 
  */
  private def generateSetConstraints(prpStruct : Expr): Expr = {
    val And(constraints) = prpStruct
    val variables = variablesOf(prpStruct).filter(p => p.getType match {case ListType(_) => true ; case _ => false})
    //Ugly :P
    val types = variables.map(_.getType match {case ListType(inner) => { Some(inner)}; case _ => None}).filter(p => p != None).map(_.get)

    //Step 1 : if there is no more than 1 list variable it does nothing

    //Step 2 : If there is more than 1 list does something

    //Step 3 : Adds Sigma(nil) == {nil} for each case and each type. And sigma(y) = {y} union...
    val sigmaNils = types.map{ tpe =>
      val nil = NilList(tpe)
      val sigma = Sigma(nil)
      val set = FiniteSet(nil :: Nil).setType(sigma.getType)
      Equals(sigma, set)
    }

    val sigmaEq = variables.map { v =>
      val sigma = Sigma(Variable(v))
      val setV = FiniteSet(Variable(v) :: Nil)
      Equals(sigma, setV)
    }

    val otherCnstrs = constraints.map(simpleToBapaConversions(_))



    //Step 4 : Existentially quantify over Segs

    And((sigmaNils ++ sigmaEq ++ otherCnstrs).toSeq)
  }

  private def simpleToBapaConversions(e : Expr): Expr = {
    def c0(e : Expr): Expr = e match {
       case Equals(list, NilList(_)) => Equals(SetCardinality(Sigma(list)), IntLiteral(1))
       case Equals(NilList(_), list) => Equals(SetCardinality(Sigma(list)), IntLiteral(1))
       case IsSubList(list1, list2) => println(list1.getType +" || "+list2.getType); Or(Seq(SubsetOf(Sigma(list1), Sigma(list2)),Equals(Sigma(list1), Sigma(list2))))
       case Not(e) => Not(c0(e))
       case Or(seq) => Or(seq.map(c0))
       //There shouldn't be any and here, e should be a clause !
       case _ => e
    }
    c0(e)
  }


  def rewriteCnstr(expression : Expr) : (Expr,Map[Expr,Expr]) = {
    
    val clauses : Set[Expr] = groundClauses(elimCons(expression))
    println("Clauses : ")
    println(clauses)

   
    val instances = clauses.map(instantiateAxioms(_)).flatten

    println("Axioms instantiation : ")
    println(instances)

    val rewCnstr = groundClauses(And((instances ++ clauses).toSeq))


    println("Rewritten Constraints : ")
    println(rewCnstr)

    val setCnstrs = generateSetConstraints(And(rewCnstr.toSeq))

    println("Set Constraints : ")
    println(setCnstrs)

    (setCnstrs, Map())
  }

  def reconstructModel(model : Map[Identifier,Expr], meta : Map[Expr,Expr]) : Map[Identifier,Expr] = {
  	sys.error("TODO")
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
    K_e = K_FLSf \T_0
    */
    lazy val K_FLSf : Set[Axiom] = Set(Pure, NoCycle1, NoCycle2, Refl, Trans, AntiSym,
                                       Total, UnfoldL, UnfoldR, GCS1, GCS2, GCS3)
    lazy val T_0 : Set[Axiom] = Set(NoCycle1, Refl, Trans, AntiSym, Total)
    lazy val K_e : Set[Axiom] = K_FLSf -- T_0 - NoCycle2// - UnfoldL


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