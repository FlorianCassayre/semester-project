package theory

trait ZFCRules extends ZFCTheory {

  def ruleEqForall(thm: Theorem, z: Id): Theorem = thm.formula match {
    case Equals(x, y) =>
      val v = SetVariable(z)
      Theorem(Forall(v, Iff(Inclusion(v, x), Inclusion(v, y))))
  }

  def ruleForallEq(thm: Theorem): Theorem = thm.formula match {
    case Forall(SetVariable(v0), Iff(Inclusion(SetVariable(v1), x), Inclusion(SetVariable(v2), y))) if v0 == v1 && v0 == v2 =>
      Theorem(Equals(x, y))
  }



  def axiomP(x: AnySet, y: AnySet): Theorem = {
    val pair = PairSet(x, y)
    Theorem(And(Inclusion(x, pair), Inclusion(y, pair)))
  }

  def axiomN(x: AnySet): Theorem = Theorem(Not(Inclusion(x, EmptySet)))


}
