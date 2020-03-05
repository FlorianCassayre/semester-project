package theory.fol

trait FOL {

  type Id = String

  type Theory

  trait Named {
    val id: Id
  }

  abstract class Formula {

  }
  case class Variable(id: Id) extends Formula with Named
  case class Implies[P <: Formula, Q <: Formula](x: P, y: Q) extends Formula
  case class Not[P <: Formula](x: P) extends Formula
  case class Iff[P <: Formula, Q <: Formula](x: P, y: Q) extends Formula
  case class Or[P <: Formula, Q <: Formula](x: P, y: Q) extends Formula
  case class And[P <: Formula, Q <: Formula](x: P, y: Q) extends Formula
  case object False extends Formula
  type False = False.type
  case object True extends Formula
  type True = True.type
  case class Equals[X <: Theory, Y <: Theory](a: X, b: Y) extends Formula

  object ->: { def unapply[P <: Formula, Q <: Formula](arg: P ->: Q): Option[(P, Q)] = Some(arg.x, arg.y) }
  object ~ { def unapply[P <: Formula](arg: ~[P]): Option[P] = Some(arg.x) }
  object <-> { def unapply[P <: Formula, Q <: Formula](arg: P <-> Q): Option[(P, Q)] = Some(arg.x, arg.y) }
  object \/ { def unapply[P <: Formula, Q <: Formula](arg: P \/ Q): Option[(P, Q)] = Some(arg.x, arg.y) }
  object /\ { def unapply[P <: Formula, Q <: Formula](arg: P /\ Q): Option[(P, Q)] = Some(arg.x, arg.y) }
  object === { def unapply[S <: Theory, T <: Theory](arg: S === T): Option[(S, T)] = Some(arg.a, arg.b) }

  final class ExtendedFormula[F <: Formula](formula: F) {
    def ->:[P <: Formula](that: P): P ->: F = Implies(that, formula) // Special, due to right associativity
    def <->[P <: Formula](that: P): F <-> P = Iff(formula, that)
    def /\[P <: Formula](that: P): F /\ P = And(formula, that)
    def \/[P <: Formula](that: P): F \/ P = Or(formula, that)
    def unary_~ : ~[F] = Not(formula)
  }
  implicit def formulaToExtended[F <: Formula](formula: F): ExtendedFormula[F] = new ExtendedFormula[F](formula)

  type ->:[P <: Formula, Q <: Formula] = Implies[P, Q]
  type ~[P <: Formula] = Not[P]
  type <->[P <: Formula, Q <: Formula] = Iff[P, Q]
  type \/[P <: Formula, Q <: Formula] = Or[P, Q]
  type /\[P <: Formula, Q <: Formula] = And[P, Q]
  type ===[T <: Theory, S <: Theory] = Equals[T, S]

  final class Theorem[+F <: Formula] private(val formula: F) {
    override def toString: String = formula.toString
  }
  object Theorem {
    private[theory] def apply[F <: Formula](formula: F): Theorem[F] = new Theorem(formula)
  }

  // Modus ponens shorthands
  final class ImpliesTheorem[P <: Formula, Q <: Formula](theorem: Theorem[P ->: Q]) {
    def apply(p: Theorem[P]): Theorem[Q] = impliesModusPonens(theorem, p)
  }
  implicit def theoremToImplies[P <: Formula, Q <: Formula](theorem: Theorem[P ->: Q]): ImpliesTheorem[P, Q] =
    new ImpliesTheorem[P, Q](theorem)
  final class IffTheorem[P <: Formula, Q <: Formula](theorem: Theorem[P <-> Q]) {
    def apply(p: Theorem[P]): Theorem[Q] = iffModusPonens(theorem, p)
  }
  implicit def theoremToIff[P <: Formula, Q <: Formula](theorem: Theorem[P <-> Q]): IffTheorem[P, Q] =
    new IffTheorem[P, Q](theorem)


  def impliesModusPonens[P <: Formula, Q <: Formula](pq: Theorem[P ->: Q], p: Theorem[P]): Theorem[Q]
  def iffModusPonens[P <: Formula, Q <: Formula](pq: Theorem[P <-> Q], p: Theorem[P]): Theorem[Q]

}
