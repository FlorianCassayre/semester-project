import org.scalatest.funsuite.AnyFunSuite
import theory.NBGTheorems

class TestNBG extends AnyFunSuite with NBGTheorems {

  // Shorthand
  implicit def toTheorem[F <: Formula](f: F): Theorem[F] = oops(f)

  val (p, q, r) = (Variable("p"), Variable("q"), Variable("r"))
  val (x, y, z) = (SetVariable("x"), SetVariable("y"), SetVariable("z"))
  val id = "w"
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

  test("equals is set") {
    assert(equalsIsSet(IsSet(z) /\ (z === y)).formula == IsSet(y))
  }

  test("intersect commutative") {
    assert(intersectCommutative(x, y).formula == ((x inter y) === (y inter x)))
  }

}
