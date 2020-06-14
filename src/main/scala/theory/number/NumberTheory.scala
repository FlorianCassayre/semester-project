package theory.number

import theory.fol.FOL._
import theory.fol.FOLRules._
import theory.fol.FOLTheorems._
import theory.NBGTheory._
import theory.NBGRules._
import theory.NBGTheorems._

object NumberTheory {

  sealed abstract class Expr extends Ordinal {
  }

  class NumberVariable[I <: String](override val id: I) extends Expr with Named {
    type T = NumberVariable[I]
    def canEqual(other: Any): Boolean = other.isInstanceOf[NumberVariable[_]]
    override def equals(other: Any): Boolean = other match {
      case that: NumberVariable[_] => (that canEqual this) && id == that.id
      case _ => false
    }
    override def hashCode(): Int = id.hashCode
    override def toString: Id = s"NumberVariable($id)"
  }
  object NumberVariable {
    def apply[I <: String](v: I): NumberVariable[I] = new NumberVariable(v)
    def apply[I <: String](implicit v: => ValueOf[I]): NumberVariable[I] = new NumberVariable(v.value)
    def unapply[I <: String](f: NumberVariable[I]): Option[String] = f match {
      case v: NumberVariable[I] => Some(v.id)
      case _ => None
    }
  }

  case object Zero extends Expr
  type Zero = Zero.type
  case class Succ[A <: Expr](n: A) extends Expr
  case class Plus[A <: Expr, B <: Expr](a: A, b: B) extends Expr
  case class Times[A <: Expr, B <: Expr](a: A, b: B) extends Expr

  case object Ind extends Expr
  type Ind = Ind.type

  type +[A <: Expr, B <: Expr] = Plus[A, B]
  type x[A <: Expr, B <: Expr] = Times[A, B]

  implicit class ExtendedNatural[A <: Expr](a: A) {
    def +[B <: Expr](b: B): A + B = Plus(a, b)
    def *[B <: Expr](b: B): A x B = Times(a, b)
  }

  implicit def zerotonat(a: 0): Zero = Zero
  implicit def onetonat(a: 1): Succ[Zero] = Succ(a - 1)
  implicit def twotonat(a: 2): Succ[Succ[Zero]] = Succ(a - 1)

}
