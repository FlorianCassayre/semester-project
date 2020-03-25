package theory.fol

import java.util.concurrent.atomic.AtomicBoolean

trait FOL {

  type Id = String

  type Theory

  trait Named {
    val id: Id
  }

  abstract class Formula {

  }
  class Variable[I <: String](override val id: I) extends Formula with Named {
    def canEqual(other: Any): Boolean = other.isInstanceOf[Variable[_]]
    override def equals(other: Any): Boolean = other match {
      case that: Variable[_] => (that canEqual this) && id == that.id
      case _ => false
    }
    override def hashCode(): Int = id.hashCode
    override def toString: Id = s"Variable($id)"
  }
  object Variable {
    def apply[I <: String](v: I): Variable[I] = new Variable(v)
    def apply[I <: String](implicit v: => ValueOf[I]): Variable[I] = new Variable(v.value)
  }
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

  class TheoremContext(val invalid: Set[AtomicBoolean], val dirty: Boolean)

  final class Theorem[+F <: Formula] private[FOL] (f: F, private[fol] val context: TheoremContext) {
    private[FOL] def checkState(): Unit = {
      if(!isValid) {
        throw new IllegalStateException("Illegal theorem")
      }
    }
    def formula: F = {
      checkState()
      f
    }
    def isValid: Boolean = context.invalid.forall(!_.get())
    def isDirty: Boolean = context.dirty
    override def toString: String = formula.toString
  }
  object Axiom {
    private[theory] def apply[F <: Formula](formula: F, dirty: Boolean = false): Theorem[F] = new Theorem(formula, new TheoremContext(Set.empty, dirty))
    private[theory] def apply[F <: Formula](formula: F, old: Set[Theorem[_]]): Theorem[F] = {
      old.foreach(_.checkState())
      new Theorem(formula, new TheoremContext(old.flatMap(_.context.invalid), old.exists(_.context.dirty)))
    }
    private[theory] def apply[F <: Formula](formula: F, dirty: Boolean, refs: Set[AtomicBoolean]): Theorem[F] = new Theorem(formula, new TheoremContext(refs, dirty))
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
