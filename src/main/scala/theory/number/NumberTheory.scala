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
