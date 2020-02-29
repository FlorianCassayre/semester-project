package theory.fol

trait FOLTheorems extends FOLRules {

  override def generalModusPonens(pq: Theorem, p: Theorem): Theorem = pq.formula match {
    case Implies(_, _) => modusPonens(pq, p)
    case Iff(p1, q) if p1 == p.formula => modusPonens(modusPonens(iffToImplies1(p1, q), pq), p)
    case Iff(q, p1) if p1 == p.formula => modusPonens(modusPonens(iffToImplies2(q, p1), pq), p)
  }

  /** `p -> q` given `p <-> q`, or `F` given `F` */
  def toImplies(pq: Theorem): Theorem = pq.formula match {
    case Iff(p, q) => iffToImplies1(p, q)(pq)
    case _ => pq
  }

  /** `p -> q` given `q` */
  def addAssumption(p: Formula, q: Theorem): Theorem = addImplies(q.formula, p)(q)

  /** `p -> r` given `p [<]-> q` and `q [<]-> r` */
  def impliesTransitive(pq: Theorem, qr: Theorem): Theorem = {
    val (ipq, iqr) = (toImplies(pq), toImplies(qr))
    (ipq.formula, iqr.formula) match {
      case (Implies(p, q1), Implies(q2, r)) if q1 == q2 => impliesDistribute(p, q1, r)(addAssumption(p, qr))(ipq)
    }
  }

  /** `(q -> p -> r)` given `(p -> q -> r)` */
  def swapAssumptions(pqr: Theorem): Theorem = pqr.formula match {
    case Implies(p, Implies(q, r)) => impliesTransitive(addImplies(q, p), impliesDistribute(p, q, r)(pqr))
  }

  /** `q <-> p` given `p <-> q` */
  def iffCommutative(thm: Theorem): Theorem = thm.formula match {
    case Iff(p, q) => impliesToIff(q, p)(iffToImplies2(p, q)(thm))(iffToImplies1(p, q)(thm))
  }

  /** `(q /\ p)` given `(p /\ q)` */
  def andCommutative(thm: Theorem): Theorem = thm.formula match {
    case And(p, q) =>
      andIff(q, p)(hypothesis(q ->: p ->: False) { qpf =>
        andIff(p, q)(thm)(swapAssumptions(qpf))
      })
  }

  /** `(q \/ p)` given `(p \/ q)` */
  def orCommutative(thm: Theorem): Theorem = thm.formula match {
    case Or(p, q) =>
      orIff(q, p)(notIff(~q /\ ~p)(hypothesis(~q /\ ~p) { hyp =>
        notIff(~p /\ ~q)(orIff(p, q)(thm))(andCommutative(hyp))
      }))
  }

  /** `p <-> p` */
  def iffReflexive(p: Formula): Theorem = {
    val pp = hypothesis(p)(identity)
    impliesToIff(p, p)(pp)(pp)
  }


  /** z /\ y given x /\ y and x <-> z */
  def ruleAndLeftSubst(and: Theorem, iff: Theorem): Theorem = (and.formula, iff.formula) match {
    case (And(x1, y), Iff(x2, z)) if x1 == x2 => ???
  }

  /** x -> y /\ y -> x given x <-> y */
  def ruleIffAndImplies(thm: Theorem): Theorem = thm.formula match {
    case Iff(x, y) => ???
  }


}
