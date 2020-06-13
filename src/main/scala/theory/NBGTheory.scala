package theory

import theory.fol.FOL._
import theory.fol.FOLRules._
import theory.fol.FOLTheorems._

object NBGTheory {

  sealed abstract class AnySet {
  }

  class SetVariable[I <: String](override val id: I) extends AnySet with Named {
    type T = SetVariable[I]
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
    def unapply[I <: String](f: SetVariable[I]): Option[String] = f match {
      case v: SetVariable[I] => Some(v.id)
      case _ => None
    }
  }

  case class Member[A <: AnySet, B <: AnySet](a: A, b: B) extends Formula
  case class SubsetEqual[A <: AnySet, B <: AnySet](a: A, b: B) extends Formula
  case class SubsetStrict[A <: AnySet, B <: AnySet](a: A, b: B) extends Formula

  case class IsSet[A <: AnySet](s: A) extends Formula

  case object EmptySet extends AnySet
  type EmptySet = EmptySet.type

  case class PairSet[A <: AnySet, B <: AnySet](a: A, b: B) extends AnySet
  case class SingletonSet[A <: AnySet](a: A) extends AnySet

  case class OrderedPair[A <: AnySet, B <: AnySet](a: A, b: B) extends AnySet

  case object MemberRelation extends AnySet
  type MemberRelation = MemberRelation.type
  case class Intersect[A <: AnySet, B <: AnySet](a: A, b: B) extends AnySet
  case class Complement[A <: AnySet](a: A) extends AnySet
  case class Domain[A <: AnySet](a: A) extends AnySet

  case class Union[A <: AnySet, B <: AnySet](a: A, b: B) extends AnySet
  case class Difference[A <: AnySet, B <: AnySet](a: A, b: B) extends AnySet
  case object Universe extends AnySet
  type Universe = Universe.type

  case class Product[A <: AnySet, B <: AnySet](a: A, b: B) extends AnySet
  case class Relation[A <: AnySet](a: A) extends Formula
  case class Power[A <: AnySet](a: A) extends AnySet
  case class Sum[A <: AnySet](a: A) extends AnySet

  case object Identity extends AnySet
  type Identity = Identity.type

  case class Fnc[A <: AnySet](a: A) extends Formula

  case object Infinity extends AnySet
  type Infinity = Infinity.type

  case class Inverse[A <: AnySet](a: A) extends AnySet
  case class Range[A <: AnySet](a: A) extends AnySet

  case object Russell extends AnySet
  type Russell = Russell.type

  abstract class RelationalProperty[X <: AnySet, Y <: AnySet](x: X, y: Y) extends Formula
  case class Irreflexive[X <: AnySet, Y <: AnySet](x: X, y: Y) extends RelationalProperty[X, Y](x, y)
  case class Transitive[X <: AnySet, Y <: AnySet](x: X, y: Y) extends RelationalProperty[X, Y](x, y)
  case class PartialOrder[X <: AnySet, Y <: AnySet](x: X, y: Y) extends RelationalProperty[X, Y](x, y)
  case class Connected[X <: AnySet, Y <: AnySet](x: X, y: Y) extends RelationalProperty[X, Y](x, y)
  case class TotalOrder[X <: AnySet, Y <: AnySet](x: X, y: Y) extends RelationalProperty[X, Y](x, y)
  case class WellOrder[X <: AnySet, Y <: AnySet](x: X, y: Y) extends RelationalProperty[X, Y](x, y)


  abstract class SkolemFunction[I <: String] extends AnySet {
    protected val v: ValueOf[I]
    def name: I = v.value
  }

  case class SkolemConstant[I <: String]()(implicit protected val v: ValueOf[I]) extends SkolemFunction[I] {
    override def toString: String = v.value.toString
  }
  case class SkolemFunction1[I <: Id, A <: AnySet](a: A)(implicit val v: ValueOf[I]) extends SkolemFunction[I] {
    override def toString: String = s"${v.value}($a)"
  }
  case class SkolemFunction2[I <: Id, A <: AnySet, B <: AnySet](a: A, b: B)(implicit val v: ValueOf[I]) extends SkolemFunction[I] {
    override def toString: String = s"${v.value}($a,$b)"
  }
  case class SkolemFunction3[I <: Id, A <: AnySet, B <: AnySet, C <: AnySet](a: A, b: B, c: C)(implicit val v: ValueOf[I]) extends SkolemFunction[I] {
    override def toString: String = s"${v.value}($a,$b,$c)"
  }

  abstract class Ordinal extends AnySet // Further work

  final class ExtendedSet[S <: AnySet](set: S) {
    // http://asciimath.org/
    def ===[T <: AnySet](that: T): S === T = Equals(set, that)
    def =!=[T <: AnySet](that: T): ~[S === T] = ~Equals(set, that)
    def in[T <: AnySet](that: T): Member[S, T] = Member(set, that)
    def notin[T <: AnySet](that: T): ~[Member[S, T]] = ~Member(set, that)
    def sub[T <: AnySet](that: T): SubsetStrict[S, T] = SubsetStrict(set, that)
    def notsub[T <: AnySet](that: T): ~[SubsetStrict[S, T]] = ~SubsetStrict(set, that)
    def sube[T <: AnySet](that: T): SubsetEqual[S, T] = SubsetEqual(set, that)
    def notsube[T <: AnySet](that: T): ~[SubsetEqual[S, T]] = ~SubsetEqual(set, that)
    def inter[T <: AnySet](that: T): Intersect[S, T] = Intersect(set, that)
    def unary_- : -[S] = Complement(set)
    def union[T <: AnySet](that: T): Union[S, T] = Union(set, that)
    def diff[T <: AnySet](that: T): Difference[S, T] = Difference(set, that)
    def irr[T <: AnySet](that: T): Irreflexive[S, T] = Irreflexive(set, that)
    def tr[T <: AnySet](that: T): Transitive[S, T] = Transitive(set, that)
    def part[T <: AnySet](that: T): PartialOrder[S, T] = PartialOrder(set, that)
    def con[T <: AnySet](that: T): Connected[S, T] = Connected(set, that)
    def tot[T <: AnySet](that: T): TotalOrder[S, T] = TotalOrder(set, that)
  }
  implicit def setToExtended[S <: AnySet](set: S): ExtendedSet[S] = new ExtendedSet[S](set)

  type -[X <: AnySet] = Complement[X]

}
