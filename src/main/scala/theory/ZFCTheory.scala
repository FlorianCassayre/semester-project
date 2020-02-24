package theory

import theory.fol.FOLTheorems

trait ZFCTheory extends FOLTheorems {

  override type Theory = AnySet

  sealed abstract class AnySet {

  }
  case object EmptySet extends AnySet
  case class SetVariable(id: Id) extends AnySet with Named
  case class PairSet(a: AnySet, b: AnySet) extends AnySet

  case class Inclusion(a: AnySet, b: AnySet) extends Formula
  case class SubsetEqual(a: AnySet, b: AnySet) extends Formula
  case class SubsetStrict(a: AnySet, b: AnySet) extends Formula

  def SingletonSet(a: AnySet): AnySet = PairSet(a, a)
  def OrderedPair(a: AnySet, b: AnySet): AnySet = PairSet(a, PairSet(a, b))
  def SingletonPair(a: AnySet): AnySet = a

}
