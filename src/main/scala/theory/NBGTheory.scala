package theory

import theory.fol.FOLTheorems

trait NBGTheory extends FOLTheorems {

  override type Theory = AnySet

  sealed abstract class AnySet {
  }
  case object EmptySet extends AnySet
  type EmptySet = EmptySet.type
  class SetVariable[I <: String](override val id: I) extends AnySet with Named {
    def canEqual(other: Any): Boolean = other.isInstanceOf[SetVariable[_]]
    override def equals(other: Any): Boolean = other match {
      case that: SetVariable[_] => (that canEqual this) && id == that.id
      case _ => false
    }
    override def hashCode(): Int = id.hashCode
    override def toString: Id = s"SetVariable($id)"
  }
  object SetVariable {
    def apply[I <: String](id: I): SetVariable[I] = new SetVariable(id)
    def apply[I <: String](implicit v: => ValueOf[I]): SetVariable[I] = new SetVariable(v.value)
  }

  case class Member[A <: AnySet, B <: AnySet](a: A, b: B) extends Formula
  case class SubsetEqual[A <: AnySet, B <: AnySet](a: A, b: B) extends Formula
  case class SubsetStrict[A <: AnySet, B <: AnySet](a: A, b: B) extends Formula

  case class IsSet[A <: AnySet](s: A) extends Formula

  case class PairSet[A <: AnySet, B <: AnySet](a: A, b: B) extends AnySet
  case class SingletonSet[A <: AnySet](a: A) extends AnySet

  case class OrderedPair[A <: AnySet, B <: AnySet](a: A, b: B) extends AnySet

  case class Intersect[A <: AnySet, B <: AnySet](a: A, b: B) extends AnySet
  case class Complement[A <: AnySet](a: A) extends AnySet
  case class Domain[A <: AnySet](a: A) extends AnySet

  case class Union[A <: AnySet, B <: AnySet](a: A, b: B) extends AnySet
  case class Difference[A <: AnySet, B <: AnySet](a: A, b: B) extends AnySet
  case object Universe extends AnySet
  type Universe = Universe.type

  case class SkolemConstant[I <: String]()(implicit v: ValueOf[I]) extends AnySet
  case class SkolemFunction1[I <: Id, A <: AnySet](a: A)(implicit v: ValueOf[I]) extends AnySet
  case class SkolemFunction2[I <: Id, A <: AnySet, B <: AnySet](a: A, b: B)(implicit v: ValueOf[I]) extends AnySet

  final class ExtendedSet[S <: AnySet](set: S) {
    // http://asciimath.org/
    def ===[T <: AnySet](that: T): S === T = Equals(set, that)
    def in[T <: AnySet](that: T): Member[S, T] = Member(set, that)
    def sub[T <: AnySet](that: T): SubsetStrict[S, T] = SubsetStrict(set, that)
    def sube[T <: AnySet](that: T): SubsetEqual[S, T] = SubsetEqual(set, that)
    def inter[T <: AnySet](that: T): Intersect[S, T] = Intersect(set, that)
    def unary_- : Complement[S] = Complement(set)
    def union[T <: AnySet](that: T): Union[S, T] = Union(set, that)
    def diff[T <: AnySet](that: T): Difference[S, T] = Difference(set, that)
  }
  implicit def setToExtended[S <: AnySet](set: S): ExtendedSet[S] = new ExtendedSet[S](set)

  type -[X <: AnySet] = Complement[X]

}
