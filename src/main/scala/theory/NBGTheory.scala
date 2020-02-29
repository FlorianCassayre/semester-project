package theory

import theory.fol.FOLTheorems

trait NBGTheory extends FOLTheorems {

  override type Theory = AnySet

  sealed abstract class AnySet {
    // http://asciimath.org/
    def ===(that: AnySet): Formula = Equals(this, that)
    def in(that: AnySet): Formula = Member(this, that)
    def sub(that: AnySet): Formula = SubsetStrict(this, that)
    def sube(that: AnySet): Formula = SubsetEqual(this, that)
  }
  case object EmptySet extends AnySet
  case class SetVariable(id: Id) extends AnySet with Named
  case class PairSet(a: AnySet, b: AnySet) extends AnySet

  case class Member(a: AnySet, b: AnySet) extends Formula
  case class SubsetEqual(a: AnySet, b: AnySet) extends Formula
  case class SubsetStrict(a: AnySet, b: AnySet) extends Formula

  case class IsSet(s: AnySet) extends Formula
  case class IsClass(s: AnySet) extends Formula

  case class SingletonSet(s: AnySet) extends Formula
  case class OrderedPair(a: AnySet, b: AnySet) extends Formula
  case class SingletonPair(a: AnySet)

}
