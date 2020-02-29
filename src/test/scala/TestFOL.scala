import org.scalatest.funsuite.AnyFunSuite
import theory.fol.FOLTheorems

class TestFOL extends AnyFunSuite with FOLTheorems {

  val (p, q, r) = (Variable("p"), Variable("q"), Variable("r"))

  test("general modus ponens") {
    def check(f: (Formula, Formula) => Formula): Unit = assert(generalModusPonens(oops(f(p, q)), oops(p)).formula == q)
    check(_ ->: _)
    check(_ <-> _)
    check((a, b) => b <-> a)
  }

}
