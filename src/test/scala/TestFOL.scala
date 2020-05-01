import org.scalatest.funsuite.AnyFunSuite
import theory.fol.FOLTheorems

class TestFOL extends ProofTestSuite with FOLTheorems {

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
    addImplies(p, q) =?= p ->: q ->: p
  }

  test("implies distribute") {
    impliesDistribute(p, q, r) =?= (p ->: q ->: r) ->: (p ->: q) ->: (p ->: r)
  }

  test("iff to implies") {
    toImplies(p <-> q) =?= p ->: q
  }

  test("add assumption") {
    addAssumption(p, q) =?= p ->: q
  }

  test("implies transitive") {
    impliesTransitive(p ->: q, q ->: r) =?= p ->: r
  }

  test("swap assumptions") {
    swapAssumptions(p ->: q ->: r) =?= q ->: p ->: r
  }

  test("iff commutative") {
    iffCommutative(p <-> q) =?= q <-> p
  }

  test("truth") {
    truth =?= True
  }

  test("and commutative") {
    andCommutative(p /\ q) =?= q /\ p
  }

  test("or commutative") {
    orCommutative(p \/ q) =?= q \/ p
  }

  test("iff reflexive") {
    iffReflexive(p) =?= p <-> p
  }

  test("and extract left") {
    andExtractLeft(p /\ q) =?= p
  }

  test("and combine") {
    andCombine(p, q) =?= p /\ q
  }

  test("iff transitive") {
    iffTransitive(p <-> q, q <-> r) =?= p <-> r
  }

  test("implies to iff rule") {
    impliesToIffRule(p ->: q, q ->: p) =?= p <-> q
  }

  test("to double negation") {
    toDoubleNegation(p) =?= (p ->: False) ->: False
  }

  test("mixed double negation") {
    mixedDoubleNegation(p) =?= ~p ->: False
  }

  test("mixed double negation invert") {
    mixedDoubleNegationInvert(~p ->: False) =?= p
  }

  test("not unduplicate") {
    notUnduplicate(~(~p)) =?= p
  }

  test("not duplicate") {
    notDuplicate(p) =?= ~(~p)
  }

  test("double not iff") {
    doubleNotIff(p) =?= ~(~p) <-> p
  }

  test("or unduplicate") {
    orUnduplicate(p \/ p) =?= p
  }

  test("iff add not") {
    iffAddNot(p <-> q) =?= ~p <-> ~q
  }

  test("or add right") {
    orAddRight(p, q) =?= p \/ q
  }

  test("add conclusion") {
    addConclusion(p ->: q, r) =?= (q ->: r) ->: (p ->: r)
  }

  test("implies inverse") {
    impliesInverse(p ->: q) =?= ~q ->: ~p
  }

  test("implies uninverse") {
    impliesUninverse(~p ->: ~q) =?= q ->: p
  }

  test("or implies") {
    orImplies(p \/ q) =?= ~p ->: ~q ->: False
  }

  test("implies or") {
    impliesOr(~p ->: ~q ->: False) =?= p \/ q
  }

  test("or case") {
    orCase(p \/ q, p ->: r, q ->: r) =?= r
  }

  test("iff remove not") {
    iffRemoveNot(~p <-> ~q) =?= p <-> q
  }

  test("iff swap not") {
    iffSwapNot(p <-> ~q) =?= ~p <-> q
  }

  test("ex falso") {
    exFalso(p) =?= False ->: p
  }

  test("and to iff") {
    andToIff(p /\ q) =?= p <-> q
  }

  test("and associative iff") {
    andAssociativeIff(p, q, r) =?= ((p /\ q) /\ r) <-> (p /\ (q /\ r))
  }

}
