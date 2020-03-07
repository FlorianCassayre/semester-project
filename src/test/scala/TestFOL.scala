import org.scalatest.funsuite.AnyFunSuite
import theory.fol.FOLTheorems

class TestFOL extends AnyFunSuite with FOLTheorems {

  // Shorthand
  implicit def toTheorem[F <: Formula](f: F): Theorem[F] = oops(f)

  val (p, q, r) = (Variable("p"), Variable("q"), Variable("r"))

  test("add implies") {
    assert(addImplies(p, q).formula == p ->: q ->: p)
  }

  test("implies distribute") {
    assert(impliesDistribute(p, q, r).formula == (p ->: q ->: r) ->: (p ->: q) ->: (p ->: r))
  }

  test("general modus ponens") {
    assert(impliesModusPonens(p ->: q, p).formula == q)
    assert(iffModusPonens(p <-> q, p).formula == q)
  }

  test("iff to implies") {
    assert(toImplies(p <-> q).formula == p ->: q)
  }

  test("add assumption") {
    assert(addAssumption(p, q).formula == p ->: q)
  }

  test("implies transitive") {
    val pr = p ->: r
    assert(impliesTransitive(p ->: q, q ->: r).formula == pr)
  }

  test("swap assumptions") {
    assert(swapAssumptions(p ->: q ->: r).formula == q ->: p ->: r)
  }

  test("iff commutative") {
    assert(iffCommutative(p <-> q).formula == q <-> p)
  }

  test("and commutative") {
    assert(andCommutative(p /\ q).formula == q /\ p)
  }

  test("or commutative") {
    assert(orCommutative(p \/ q).formula == q \/ p)
  }

  test("iff reflexive") {
    assert(iffReflexive(p).formula == p <-> p)
  }

  test("and extract left") {
    assert(andExtractLeft(p /\ q).formula == p)
  }

  test("and combine") {
    assert(andCombine(p, q).formula == p /\ q)
  }

  test("iff transitive") {
    assert(iffTransitive(p <-> q, q <-> r).formula == p <-> r)
  }

  test("to double negation") {
    assert(toDoubleNegation(p).formula == (p ->: False) ->: False)
  }

  test("mixed double negation") {
    assert(mixedDoubleNegation(p).formula == ~p ->: False)
  }

  test("not unduplicate") {
    assert(notUnduplicate(~(~p)).formula == p)
  }

  test("not duplicate") {
    assert(notDuplicate(p).formula == ~(~p))
  }

  test("and duplicate") {
    assert(andDuplicate(p).formula == p /\ p)
  }

  test("or unduplicate") {
    assert(orUnduplicate(p \/ p).formula == p)
  }

  test("iff add not") {
    assert(iffAddNot(p <-> q).formula == ~p <-> ~q)
  }

  test("or duplicate") {
    assert(orDuplicate(p).formula == p \/ p)
  }
}
