package theory.fol

trait FOLTheorems extends FOLRules {

  /** `p -> q -> p` */
  def addImplies[P <: Formula, Q <: Formula](p: P, q: Q): Theorem[P ->: Q ->: P] = hypothesis(p)(tp => hypothesis(q)(_ => tp))

  /** `(p -> q -> r) -> (p -> q) -> (p -> r)` */
  def impliesDistribute[P <: Formula, Q <: Formula, R <: Formula](p: P, q: Q, r: R): Theorem[(P ->: Q ->: R) ->: (P ->: Q) ->: (P ->: R)] =
    hypothesis(p ->: q ->: r)(pqr => hypothesis(p ->: q)(pq => hypothesis(p)(tp => pqr(tp)(pq(tp)))))

  /** `p -> q` given `p <-> q` */
  def toImplies[P <: Formula, Q <: Formula](pq: Theorem[P <-> Q]): Theorem[P ->: Q] = {
    theoremToImplies(iffToImplies1(pq.formula.x, pq.formula.y))(pq)
  }

  /** `p -> q` given `q` */
  def addAssumption[P <: Formula, Q <: Formula](p: P, q: Theorem[Q]): Theorem[P ->: Q] = addImplies(q.formula, p)(q)

  /** `p -> r` given `p -> q` and `q -> r` */
  def impliesTransitive[P <: Formula, Q <: Formula, R <: Formula](pq: Theorem[P ->: Q], qr: Theorem[Q ->: R]): Theorem[P ->: R] =
    (pq.formula, qr.formula) match {
      case (p ->: q1, q2 ->: r) if q1 == q2 => impliesDistribute[P, Q, R](p, q1, r)(addAssumption(p, qr))(pq)
    }

  /** `p -> r` given `p <-> q` and `q -> r` */
  def impliesTransitive1[P <: Formula, Q <: Formula, R <: Formula](pq: Theorem[P <-> Q], qr: Theorem[Q ->: R]): Theorem[P ->: R] =
    impliesTransitive(toImplies(pq), qr)

  /** `p -> r` given `p -> q` and `q <-> r` */
  def impliesTransitive2[P <: Formula, Q <: Formula, R <: Formula](pq: Theorem[P ->: Q], qr: Theorem[Q <-> R]): Theorem[P ->: R] =
    impliesTransitive(pq, toImplies(qr))

  /** `p -> r` given `p <-> q` and `q <-> r` */
  def impliesTransitive3[P <: Formula, Q <: Formula, R <: Formula](pq: Theorem[P <-> Q], qr: Theorem[Q <-> R]): Theorem[P ->: R] =
    impliesTransitive(toImplies(pq), toImplies(qr))

  /** `(q -> p -> r)` given `(p -> q -> r)` */
  def swapAssumptions[P <: Formula, Q <: Formula, R <: Formula](pqr: Theorem[P ->: Q ->: R]): Theorem[Q ->: P ->: R] =
    pqr.formula match {
      case p ->: q ->: r =>
        impliesTransitive(addImplies(q, p), impliesDistribute(p, q, r)(pqr))
    }

  /** `q <-> p` given `p <-> q` */
  def iffCommutative[P <: Formula, Q <: Formula](thm: Theorem[P <-> Q]): Theorem[Q <-> P] = {
    val (p, q) = (thm.formula.x, thm.formula.y)
    impliesToIff(q, p)(iffToImplies2(p, q)(thm))(iffToImplies1(p, q)(thm))
  }

  /** `(q /\ p)` given `(p /\ q)` */
  def andCommutative[P <: Formula, Q <: Formula](thm: Theorem[P /\ Q]): Theorem[Q /\ P] = thm.formula match {
    case p /\ q =>
      iffCommutative(andIff(q, p))(hypothesis(q ->: p ->: False) { qpf =>
        andIff(p, q)(thm)(swapAssumptions(qpf))
      })
  }

  /** `(q \/ p)` given `(p \/ q)` */
  def orCommutative[P <: Formula, Q <: Formula](thm: Theorem[P \/ Q]): Theorem[Q \/ P] = thm.formula match {
    case p \/ q =>
      iffCommutative(orIff(q, p))(iffCommutative(notIff(~q /\ ~p))(hypothesis(~q /\ ~p) { hyp =>
        notIff(~p /\ ~q)(orIff(p, q)(thm))(andCommutative(hyp))
      }))
  }

  /** `p <-> p` */
  def iffReflexive[P <: Formula](p: P): Theorem[P <-> P] = {
    val pp = hypothesis(p)(identity)
    impliesToIff(p, p)(pp)(pp)
  }

  /** `p` given `p /\ q` */
  def andExtractLeft[P <: Formula, Q <: Formula](thm: Theorem[P /\ Q]): Theorem[P] = thm.formula match {
    case p /\ q =>
      doubleNegation(p)(hypothesis(p ->: False)(pf =>
        andIff(p, q)(thm)(hypothesis(p)(tp =>
          addAssumption(q, pf(tp))
        ))
      ))
  }

  /** `p /\ q` given `p` and `q` */
  def andCombine[P <: Formula, Q <: Formula](tp: Theorem[P], tq: Theorem[Q]): Theorem[P /\ Q] = {
    val (p, q) = (tp.formula, tq.formula)
    iffCommutative(andIff(p, q))(hypothesis(p ->: q ->: False)(pqf => pqf(tp)(tq)))
  }

  /** `p <-> r` given `p <-> q` and `q <-> r` */
  def iffTransitive[P <: Formula, Q <: Formula, R <: Formula](pq: Theorem[P <-> Q], qr: Theorem[Q <-> R]): Theorem[P <-> R] = (pq.formula, qr.formula) match {
    case (p <-> q1, q2 <-> r) if q1 == q2 =>
      impliesToIff(p, r)(impliesTransitive(toImplies(pq), toImplies(qr)))(impliesTransitive(toImplies(iffCommutative(qr)), toImplies(iffCommutative(pq))))
  }

  /** `p <-> q` given `p -> q` and `q -> p` */
  def impliesToIffRule[P <: Formula, Q <: Formula](pq: Theorem[P ->: Q], qp: Theorem[Q ->: P]): Theorem[P <-> Q] = (pq.formula, qp.formula) match {
    case (p1 ->: q1, q2 ->: p2) if p1 == p2 && q1 == q2 =>
    impliesToIff(p1, q1)(pq)(qp)
  }

  def impliesToIffForallRule[P <: Formula, Q <: Formula, N <: Named](pq: Theorem[Forall[N, P ->: Q]], qp: Theorem[Forall[N, Q ->: P]]): Theorem[Forall[N, P <-> Q]] = {
    val combined = forallAnd(pq, qp)
    forall(combined)(all => impliesToIffRule(andExtractLeft(all), andExtractLeft(andCommutative(all))))
  }

}
