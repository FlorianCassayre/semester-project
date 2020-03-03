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

  final class ExtendedSet[S <: AnySet](set: S) {
    // http://asciimath.org/
    def ===[T <: AnySet](that: T): S === T = Equals(set, that)
    def in[T <: AnySet](that: T): Member[S, T] = Member(set, that)
    def sub[T <: AnySet](that: T): SubsetStrict[S, T] = SubsetStrict(set, that)
    def sube[T <: AnySet](that: T): SubsetEqual[S, T] = SubsetEqual(set, that)
  }
  implicit def setToExtended[S <: AnySet](set: S): ExtendedSet[S] = new ExtendedSet[S](set)

}
