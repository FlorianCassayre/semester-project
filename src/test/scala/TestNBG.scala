import org.scalatest.Ignore
import org.scalatest.funsuite.AnyFunSuite
import theory.NBGTheorems

class TestNBG extends AnyFunSuite with NBGTheorems {

  // Shorthand
  implicit def toTheorem[F <: Formula](f: F): Theorem[F] = oops(f)

  val (p, q, r) = (Variable["p"], Variable["q"], Variable["r"])
  val (x, y, z, u, v) = (SetVariable["x"], SetVariable["y"], SetVariable["z"], SetVariable["u"], SetVariable["v"])
  type W = "w"
  val id = implicitly[ValueOf[W]].value
  val w = SetVariable(id)

  test("equals subset") {
    assert(equalsSubset(x, y).formula == ((x === y) <-> ((x sube y) /\ (y sube x))))
  }

  test("equals reflexive") {
    assert(equalsReflexive(x).formula == (x === x))
  }

  test("equals symmetric") {
    assert(equalsSymmetric(x === y).formula == (y === x))
  }

  test("equals transitive") {
    assert(equalsTransitive(x === y, y === z).formula == (x === z))
  }

  test("equals symmetric iff") {
    assert(equalsSymmetricIff(x, y).formula == (x === y) <-> (y === x))
  }

  test("equals is set") {
    assert(equalsIsSet(IsSet(z) /\ (z === y)).formula == IsSet(y))
  }

  test("pair commutative") {
    assert(pairCommutative(x, y).formula == (IsSet(x) ->: IsSet(y) ->: (PairSet(x, y) === PairSet(y, x))))
  }

  test("singleton equals") {
    assert(singletonEquals(x, y).formula == IsSet(x) ->: IsSet(y) ->: ((x in SingletonSet(y)) <-> (x === y)))
  }

  test("singleton membership commutative") {
    assert(singletonMembershipCommutative(x, y).formula == IsSet(x) ->: IsSet(y) ->: ((x in SingletonSet(y)) <-> (y in SingletonSet(x))))
  }

  test("singleton congruence") {
    assert(singletonCongruence(x, y).formula == (IsSet(x) ->: IsSet(y) ->: ((SingletonSet(x) === SingletonSet(y)) <-> (x === y))))
  }

  test("ordered pair to equals") {
    assert(orderedPairToEquals(x, y, u, v).formula == IsSet(x) ->: IsSet(y) ->: IsSet(u) ->: IsSet(v) ->: (OrderedPair(x, y) === OrderedPair(u, v)) ->: ((x === u) /\ (y === v)))
  }

  test("union contains") {
    assert(unionContains(x, y, z).formula == IsSet(z) ->: ((z in (x union y)) <-> ((z in x) \/ (z in y))))
  }

  test("universe contains") {
    assert(universeContains(x).formula == IsSet(x) ->: (x in Universe))
  }

  test("difference contains") {
    assert(differenceContains(x, y, z).formula == IsSet(z) ->: ((z in (x diff y)) <-> ((z in x) /\ ~(z in y))))
  }

  test("intersect commutative") {
    assert(intersectCommutative(x, y).formula == ((x inter y) === (y inter x)))
  }

  test("complement congruence") {
    assert(complementCongruence(x, y).formula == ((x === y) <-> (-x === -y)))
  }

  test("union commutative") {
    assert(unionCommutative(x, y).formula == ((x union y) === (y union x)))
  }

  test("subset intersection") {
    assert(subsetIntersect(x, y).formula == ((x sube y) <-> ((x inter y) === x)))
  }

  ignore("subset union") {
    assert(subsetUnion(x, y).formula == ((x sube y) <-> ((x union y) === y)))
  }

  ignore("intersection associative") {
    assert(intersectAssociative(x, y, z).formula == (((x inter y) inter z) === (x inter (y inter z))))
  }

  ignore("union associative") {
    assert(unionAssociative(x, y, z).formula == (((x union y) union z) === (x union (y union z))))
  }

  test("intersection indempotent") {
    assert(intersectIndempotent(x).formula == ((x inter x) === x))
  }

  test("union indempotent") {
    assert(unionIndempotent(x).formula == ((x union x) === x))
  }

  test("intersection empty") {
    assert(intersectEmpty(x).formula == ((x inter EmptySet) === EmptySet))
  }

  test("union empty") {
    assert(unionEmpty(x).formula == ((x union EmptySet) === x))
  }

  test("intersection universe") {
    assert(intersectUniverse(x).formula == ((x inter Universe) === x))
  }

  test("union universe") {
    assert(unionUniverse(x).formula == ((x union Universe) === Universe))
  }

  ignore("union complement") {
    assert(unionComplement(x, y).formula == (-(x union y) === (-x union -y)))
  }

  ignore("intersection complement") {
    assert(intersectComplement(x, y).formula == (-(x inter y) === (-x union -y)))
  }

  test("difference self") {
    assert(differenceSelf(x).formula == ((x diff x) === EmptySet))
  }

  test("universe difference") {
    assert(universeDifference(x).formula == ((Universe diff x) === -x))
  }

  ignore("double difference") {
    assert(doubleDifference(x, y).formula == ((x diff (x diff y)) === (x inter y)))
  }

  ignore("subset difference") {
    assert(subsetDifference(x, y).formula == ((y sube -x) ->: ((x diff y) === x)))
  }

  test("double complement") {
    assert(doubleComplement(x).formula == (-(-x) === x))
  }

  test("universe complement") {
    assert(universeComplement.formula == (-Universe === EmptySet))
  }

  ignore("intersection distributivity") {
    assert(intersectDistributivity(x, y, z).formula == ((x inter (y union z)) === ((x inter y) union (x inter z))))
  }

  ignore("union distributivity") {
    assert(unionDistributivity(x, y, z).formula == ((x union (y inter z)) === ((x union y) inter (x union z))))
  }
}
