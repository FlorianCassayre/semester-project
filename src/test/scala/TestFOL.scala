import org.scalatest.funsuite.AnyFunSuite
import theory.fol.FOLTheorems

class TestFOL extends AnyFunSuite with FOLTheorems {

  // Shorthand
  implicit def toTheorem[F <: Formula](f: F): Theorem[F] = oops(f)

  val (p, q, r) = (Variable["p"], Variable["q"], Variable["r"])

  test("illegal escape") {
    var illegal: Theorem[False] = null

    val legal = assume(False) { f =>
      illegal = f // Illegal escape
      f
    }

    legal.formula // Legal access

    assertThrows[IllegalStateException] {
      val f = illegal.formula // Trying to access attribute
    }
    assertThrows[IllegalStateException] {
      val str = illegal.toString // toString
    }
    assertThrows[IllegalStateException] {
      val t = assume(False)(identity)
      t(illegal) // Composition
    }
  }

  test("illegal escape nested") {
    var illegal: Theorem[False] = null

    assume(False) { f1 =>
      assume(False) { f2 =>
        illegal = f2
        f2
      }
      f1
    }

    assertThrows[IllegalStateException] {
      val f = illegal.formula
    }
  }

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

  test("implies to iff rule") {
    assert(impliesToIffRule(p ->: q, q ->: p).formula == p <-> q)
  }

  test("to double negation") {
    assert(toDoubleNegation(p).formula == (p ->: False) ->: False)
  }

  test("mixed double negation") {
    assert(mixedDoubleNegation(p).formula == ~p ->: False)
  }

  test("mixed double negation invert") {
    assert(mixedDoubleNegationInvert(~p ->: False).formula == p)
  }

  test("not unduplicate") {
    assert(notUnduplicate(~(~p)).formula == p)
  }

  test("not duplicate") {
    assert(notDuplicate(p).formula == ~(~p))
  }

  test("double not iff") {
    doubleNotIff(~(~p) <-> p)
  }

  test("or unduplicate") {
    assert(orUnduplicate(p \/ p).formula == p)
  }

  test("iff add not") {
    assert(iffAddNot(p <-> q).formula == ~p <-> ~q)
  }

  test("or add right") {
    assert(orAddRight(p, q).formula == p \/ q)
  }

  test("add conclusion") {
    assert(addConclusion(p ->: q, r).formula == (q ->: r) ->: (p ->: r))
  }

  test("implies inverse") {
    assert(impliesInverse(p ->: q).formula == ~q ->: ~p)
  }

  test("or implies") {
    assert(orImplies(p \/ q).formula == ~p ->: ~q ->: False)
  }

  test("or case") {
    assert(orCase(p \/ q, p ->: r, q ->: r).formula == r)
  }

  test("iff remove not") {
    assert(iffRemoveNot(~p <-> ~q).formula == p <-> q)
  }

  test("iff swap not") {
    assert(iffSwapNot(p <-> ~q).formula == ~p <-> q)
  }

  test("ex falso") {
    assert(exFalso(p).formula == False ->: p)
  }

  test("and to iff") {
    assert(andToIff(p /\ q).formula == p <-> q)
  }
}
