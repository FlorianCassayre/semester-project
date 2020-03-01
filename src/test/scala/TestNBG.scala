import org.scalatest.funsuite.AnyFunSuite
import theory.NBGTheorems

class TestNBG extends AnyFunSuite with NBGTheorems {

  // Shorthand
  implicit def toTheorem(f: Formula): Theorem = oops(f)

  val (p, q, r) = (Variable("p"), Variable("q"), Variable("r"))
  val (x, y, z) = (SetVariable("x"), SetVariable("y"), SetVariable("z"))
  val id = "w"
  val w = SetVariable(id)

  /*test("equals subset") {
    assert(equalsSubset(x, y).formula == Iff(Equals(x, y), And(SubsetEqual(x, y), SubsetEqual(y, x))))
  }*/

  test("equals reflexive") {
    assert(equalsReflexive(x).formula == Equals(x, x))
  }

  test("equals symmetric") {
    assert(equalsSymmetric(Equals(x, y)).formula == Equals(y, x))
  }

  test("equals transitive") {
    assert(equalsTransitive(Equals(x, y), Equals(y, z)).formula == Equals(x, z))
  }

}
