package theory

trait ZFCTheorems extends ZFCRules {

  /** x sub y /\ y sub x given x = y */
  def ruleEqualitySubset(thm: Theorem): Theorem = thm.formula match {
    case Equals(x, y) =>
      val id = "$" // TODO fresh name
      forall(ruleEqForall(thm, id)) { t =>
        ruleIffAndImplies(t)
      }
  }

}
