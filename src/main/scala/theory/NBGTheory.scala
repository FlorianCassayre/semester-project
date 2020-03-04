package theory

import theory.fol.FOLTheorems

trait NBGTheory extends FOLTheorems {

  override type Theory = AnySet

  sealed abstract class AnySet {
  }
  case object EmptySet extends AnySet
  case class SetVariable(id: Id) extends AnySet with Named
  case class PairSet(a: AnySet, b: AnySet) extends AnySet

  case class Member[A <: AnySet, B <: AnySet](a: A, b: B) extends Formula
  case class SubsetEqual[A <: AnySet, B <: AnySet](a: A, b: B) extends Formula
  case class SubsetStrict[A <: AnySet, B <: AnySet](a: A, b: B) extends Formula

  case class IsSet(s: AnySet) extends Formula
  case class IsClass(s: AnySet) extends Formula

  case class SingletonSet(s: AnySet) extends Formula
  case class OrderedPair(a: AnySet, b: AnySet) extends Formula
  case class SingletonPair(a: AnySet)

  case class Intersect[A <: AnySet, B <: AnySet](a: A, b: B) extends AnySet
  case class Union[A <: AnySet, B <: AnySet](a: A, b: B) extends AnySet
  case class Difference[A <: AnySet, B <: AnySet](a: A, b: B) extends AnySet

  final class ExtendedSet[S <: AnySet](set: S) {
    // http://asciimath.org/
    def ===[T <: AnySet](that: T): S === T = Equals(set, that)
    def in[T <: AnySet](that: T): Member[S, T] = Member(set, that)
    def sub[T <: AnySet](that: T): SubsetStrict[S, T] = SubsetStrict(set, that)
    def sube[T <: AnySet](that: T): SubsetEqual[S, T] = SubsetEqual(set, that)
    def inter[T <: AnySet](that: T): Intersect[S, T] = Intersect(set, that)
    def union[T <: AnySet](that: T): Union[S, T] = Union(set, that)
    def diff[T <: AnySet](that: T): Difference[S, T] = Difference(set, that)
  }
  implicit def setToExtended[S <: AnySet](set: S): ExtendedSet[S] = new ExtendedSet[S](set)

}
