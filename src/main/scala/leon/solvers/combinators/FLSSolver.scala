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
class FLSSolver[+S <: Solver, T](underlying: S) extends RewritingSolver[S, Map[Expr,Expr]](underlying){
  def name = "FLS Solver"


  /** This should remove every x = Cons(y, ys) from this expr, 
      and replace them with x.head = y && x.tail = ys && x != Nil
   *
   * @param expression The negated VC 
   * @return An expression without Cons constructs
   */
  private def elimCons(expression: Expr): Expr = {
    sys.error("TODO")
  }

  /** This should return the set of ground clauses of a given expression

  * @param expression The expression after elimcons
  * @return A set of ground clauses
  */

  private def groundClauses(expression: Expr): Set[Expr] = {
    sys.error("TODO")
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


  def rewriteCnstr(expression : Expr) : (Expr,Map[Expr,Expr]) = {
  	sys.error("TODO")
  }

  def reconstructModel(model : Map[Identifier,Expr], meta : Map[Expr,Expr]) : Map[Identifier,Expr] = {
  	sys.error("TODO")
  }


  /**
    These objects instantiate axioms. Assumes that only variables of type List are given
  */
  object FLSfCompletionAxioms {
    /* Notes about the local theory extension
    Omega_e = {head, tail, gcd}
    Sigma_0 = {S_FLS, {nil, isSublist}}
    S_FLS = {bool, list data}
    K_FLSf = {Pure, NoCycle{1,2}, Refl, Trans, AntiSym, Total, UnfoldL, UnfildR, GCS{1,2,3}}
    T_0 = {NoCycle1, Refl, Trans, AntiSym, Total}
    K_e = K_FLSf \T_0
    */
    trait Axiom {
      def apply(fvs : Seq[Variable]): Option[Expr]
    }

    sealed trait UnaryAxiom extends Axiom {
      def apply(fvs : Seq[Variable]): Option[Expr] = fvs match{
        case fv :: Nil => Some(this(fv))
        case _ => None
      }
      def apply(fv : Variable): Expr
    }

    sealed trait BinaryAxiom extends Axiom {
      def apply(fvs : Seq[Variable]): Option[Expr] = fvs match {
        case fv0 :: fv1 :: Nil => Some(this(fv0,fv1))
        case _ => None
      }

      def apply(fv0 : Variable, fv1 : Variable): Expr
    }

    sealed trait TernaryAxiom extends Axiom {
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
        val ListType(inner) = x.getType
        val nilList = NilList(inner)
        val lhs = Equals(Cdr(x), nilList)
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
  }

}