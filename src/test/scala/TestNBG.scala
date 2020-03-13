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

  test("intersect commutative") {
    assert(intersectCommutative(x, y).formula == ((x inter y) === (y inter x)))
  }

  test("ordered pair to equals") {
    assert(orderedPairToEquals(x, y, u, v).formula == IsSet(x) ->: IsSet(y) ->: IsSet(u) ->: IsSet(v) ->: (OrderedPair(x, y) === OrderedPair(u, v)) ->: ((x === u) /\ (y === v)))
  }

}
