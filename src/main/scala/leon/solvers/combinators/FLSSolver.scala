package leon
package solvers
package combinators

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._



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
  //This contain the maping between a list variable and it's set of subLists
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
    val vars : Set[Variable]= variablesOf(expression).map(id => Variable(id))
    K_e.map(instantiateAxiom(vars,_)).flatten
  }

  private def instantiateAxiom(vars : Set[Variable], axiom : Axiom): Set[Expr] = axiom match {
    case axiom : UnaryAxiom => vars.map(axiom(_))
    case axiom : BinaryAxiom if(vars.size > 1) => {
      val iter = vars.sliding(2,1).map(p => p.toList)
      val ret = for(tup <- iter) yield {
        axiom(tup(0), tup(1))     
      }
      ret.toSet
    }
    case axiom : TernaryAxiom if(vars.size > 2) => {
      val iter = vars.sliding(3,1).map(p => p.toList)
      val ret = for(tup <- iter) yield {
        axiom(tup(0), tup(1), tup(2))     
      }
      ret.toSet
    }
    case _ => Set()
  }
  /** This applies the procedure described in p.14.
    @param prpStruct : The derived PRP structure
    @return the set constraint 
  */
  private def generateSetConstraints(prpStruct : Expr): Expr = {
    val groundTerms = variablesOf(prpStruct).filter(p => p.getType match {case ListType(_) => true ; case _ => false})
    //Ugly :P
    val types = groundTerms.map(_.getType match {case ListType(inner) => Some(inner); case _ => None}).filter(p => p == None).map(_.get)
    //Step 1 : if there is no more than 1 list variable it does nothing

    //Step 2 : If there is more than 1 list

    //Step 3 : Adds Sigma(nil) == {nil} for each case and each type. And
    val sigmaNils = types.map{ tpe =>
      val nil = NilList(tpe)
      val sigma = Sigma(nil)
      val set = FiniteSet(nil :: Nil).setType(sigma.getType)
      Equals(sigma, set)
    }


    //Step 4 : Existentially quantify over Segs

    prpStruct
  }


  def rewriteCnstr(expression : Expr) : (Expr,Map[Expr,Expr]) = {
    
    val clauses : Set[Expr] = groundClauses(elimCons(expression))
    println("Clauses : ")
    println(clauses)
    //Fast duct taping remove dublicates
    var instances = Set[Expr]()
    val instances0 = clauses.map(instantiateAxioms(_)).flatten
    for(i <- instances0) {println("Eq ? "+i+" --- "+instances(i) ) ;if(!instances(i)) instances += i}

    for(i <- instances0; j <- instances){
      println("Eq ? "+i+" == "+j+" --- "+i == j )
    }


    println("Axioms instantiation : ")
    println(instances)


  	sys.error("TODO")
  }

  def reconstructModel(model : Map[Identifier,Expr], meta : Map[Expr,Expr]) : Map[Identifier,Expr] = {
  	sys.error("TODO")
  }


  /**
    These objects instantiate axioms. Assumes that only variables of type List are given
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
    lazy val K_e : Set[Axiom] = K_FLSf -- T_0


    trait Axiom {
      def arity : Int
      def apply(fvs : Seq[Variable]): Option[Expr]
    }

    trait UnaryAxiom extends Axiom {
      def arity = 1
      def apply(fvs : Seq[Variable]): Option[Expr] = fvs match{
        case fv :: Nil => Some(this(fv))
        case _ => None
      }
      def apply(fv : Variable): Expr
    }

    trait BinaryAxiom extends Axiom {
      def arity = 2
      def apply(fvs : Seq[Variable]): Option[Expr] = fvs match {
        case fv0 :: fv1 :: Nil => Some(this(fv0,fv1))
        case _ => None
      }

      def apply(fv0 : Variable, fv1 : Variable): Expr
    }

    trait TernaryAxiom extends Axiom {
      def arity = 3
      def apply(fvs : Seq[Variable]): Option[Expr] = fvs match {
        case fv0 :: fv1 :: fv2 :: Nil => Some(this(fv0, fv1, fv2))
        case _ => None
      }

      def apply(fv0 : Variable, fv1 : Variable, fv2 : Variable): Expr
    }

    object Pure extends BinaryAxiom {
      def apply(x : Variable, y : Variable): Expr = {
          val tpe @ ListType(inner) = x.getType
          val heads = Equals(Car(x).setType(inner), Car(y).setType(inner))
          val tails = Equals(Cdr(x).setType(tpe), Cdr(y).setType(tpe))

          val nilList = NilList(inner)
          val rhs = Or(Seq(Equals(x,y),Equals(x,nilList), Equals(y, nilList)))
          val lhs = And(Seq(heads, tails))

          Implies(lhs, rhs)
      }
    }

    object NoCycle1 extends UnaryAxiom {
      def apply(x : Variable): Expr = {
        val ListType(inner) = x.getType
        val nilList = NilList(inner)
        IsSubList(nilList, x)
      }
    }

    object NoCycle2 extends UnaryAxiom {
      def apply(x : Variable): Expr = {
        val tpe @ ListType(inner) = x.getType
        val nilList = NilList(inner)
        val lhs = Equals(Cdr(x).setType(tpe), x)
        val rhs = Equals(x, nilList)

        Implies(lhs, rhs)
      }
    }

    object Refl extends UnaryAxiom {
      def apply(x : Variable): Expr = {
        IsSubList(x,x)
      }
    }

    object Trans extends TernaryAxiom {
      def apply(x : Variable, y : Variable, z : Variable): Expr = {
        val lhs = And(Seq(IsSubList(x,y), IsSubList(y,z)))
        val rhs = IsSubList(x,z)

        Implies(lhs, rhs)
      }
    }

    object AntiSym extends BinaryAxiom {
      def apply(x : Variable, y : Variable): Expr = {
        val lhs = And(Seq(IsSubList(x,y), IsSubList(y,x)))
        val rhs = Equals(x,y)

        Implies(x,y)
      }
    }

    object Total extends TernaryAxiom {
      def apply(x : Variable, y : Variable, z : Variable): Expr = {
        val lhs = And(Seq(IsSubList(y,x), IsSubList(z,x)))
        val rhs = Or(Seq(IsSubList(y,z), IsSubList(z,y)))

        Implies(lhs, rhs)
      }
    }

    object UnfoldL extends UnaryAxiom {
      def apply(x : Variable): Expr = {
        val tpe @ ListType(inner) = x.getType
        IsSubList(Cdr(x).setType(tpe), x)
      }
    }

    object UnfoldR extends BinaryAxiom {
      def apply(x : Variable, y : Variable): Expr = {
          val tpe @ ListType(inner) = x.getType
          val lhs = IsSubList(x,y)
          val rhs = Or(Seq(Equals(x,y), IsSubList(x, Cdr(y).setType(tpe))))

          Implies(lhs, rhs)
      }
    }

    object GCS1 extends BinaryAxiom {
      def apply(x : Variable, y : Variable): Expr = {
        IsSubList(Gcs(x,y), y)
      }
    }

    object GCS2 extends BinaryAxiom {
      def apply(x : Variable, y : Variable): Expr = {
        IsSubList(Gcs(x,y), x)
      }
    }

    object GCS3 extends TernaryAxiom {
      def apply(x : Variable, y : Variable, z : Variable): Expr = {
        val lhs = And(Seq(IsSubList(z,x), IsSubList(z, y)))
        val rhs = IsSubList(z, Gcs(x,y))

        Implies(lhs, rhs)
      }
    }

  }

}