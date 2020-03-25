package theory.fol

trait FOLTheorems extends FOLRules {

  /** `p -> q -> p` */
  def addImplies[P <: Formula, Q <: Formula](p: P, q: Q): Theorem[P ->: Q ->: P] = assume(p)(tp => assume(q)(_ => tp))

  /** `(p -> q -> r) -> (p -> q) -> (p -> r)` */
  def impliesDistribute[P <: Formula, Q <: Formula, R <: Formula](p: P, q: Q, r: R): Theorem[(P ->: Q ->: R) ->: (P ->: Q) ->: (P ->: R)] =
    assume(p ->: q ->: r)(pqr => assume(p ->: q)(pq => assume(p)(tp => pqr(tp)(pq(tp)))))

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
      iffCommutative(andIff(q, p))(assume(q ->: p ->: False) { qpf =>
        andIff(p, q)(thm)(swapAssumptions(qpf))
      })
  }

  /** `(q \/ p)` given `(p \/ q)` */
  def orCommutative[P <: Formula, Q <: Formula](thm: Theorem[P \/ Q]): Theorem[Q \/ P] = thm.formula match {
    case p \/ q =>
      iffCommutative(orIff(q, p))(iffCommutative(notIff(~q /\ ~p))(assume(~q /\ ~p) { hyp =>
        notIff(~p /\ ~q)(orIff(p, q)(thm))(andCommutative(hyp))
      }))
  }

  /** `p <-> p` */
  def iffReflexive[P <: Formula](p: P): Theorem[P <-> P] = {
    val pp = assume(p)(identity)
    impliesToIff(p, p)(pp)(pp)
  }

  /** `p` given `p /\ q` */
  def andExtractLeft[P <: Formula, Q <: Formula](thm: Theorem[P /\ Q]): Theorem[P] = thm.formula match {
    case p /\ q =>
      doubleNegation(p)(assume(p ->: False)(pf =>
        andIff(p, q)(thm)(assume(p)(tp =>
          addAssumption(q, pf(tp))
        ))
      ))
  }

  /** `p /\ q` given `p` and `q` */
  def andCombine[P <: Formula, Q <: Formula](tp: Theorem[P], tq: Theorem[Q]): Theorem[P /\ Q] = {
    val (p, q) = (tp.formula, tq.formula)
    iffCommutative(andIff(p, q))(assume(p ->: q ->: False)(pqf => pqf(tp)(tq)))
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

  /** `(p -> False) -> False` given `p` */
  def toDoubleNegation[P <: Formula](tp: Theorem[P]): Theorem[(P ->: False) ->: False] = {
    val p = tp.formula
    assume(p ->: False)(pf => pf(tp))
  }

  /** `~p -> false` given `p` */
  def mixedDoubleNegation[P <: Formula](thm: Theorem[P]): Theorem[~[P] ->: False] = {
    val p = thm.formula
    assume(~p)(np => notIff(p)(np)(thm))
  }

  /** `p` given `~p -> false` */
  def mixedDoubleNegationInvert[P <: Formula](thm: Theorem[~[P] ->: False]): Theorem[P] = {
    val p = thm.formula.x.x
    notUnduplicate(iffCommutative(notIff(~p))(thm))
  }

  /** `p` given `~~p` */
  def notUnduplicate[P <: Formula](thm: Theorem[~[~[P]]]): Theorem[P] = {
    val p = thm.formula.x.x
    doubleNegation(p)(impliesTransitive(assume(p ->: False)(pf => iffCommutative(notIff(p))(pf)), notIff(~p)(thm)))
  }

  /** `~~p` given `p` */
  def notDuplicate[P <: Formula](thm: Theorem[P]): Theorem[~[~[P]]] = {
    val p = thm.formula
    toImplies(iffCommutative(notIff(~p)))(mixedDoubleNegation(thm))
  }

  /** `p` given `p \/ p` */
  def orUnduplicate[P <: Formula](thm: Theorem[P \/ P]): Theorem[P] = thm.formula match {
    case p \/ p1 if p == p1 =>
      notUnduplicate(iffCommutative(notIff(~p))(impliesTransitive(assume(~p)(h => andCombine(h, h)), notIff(~p /\ ~p)(orIff(p, p)(thm)))))
  }

  /** `~p <-> ~q` given `p <-> q` */
  def iffAddNot[P <: Formula, Q <: Formula](thm: Theorem[P <-> Q]): Theorem[~[P] <-> ~[Q]] = {
    def lemma[A <: Formula, B <: Formula](t: Theorem[A <-> B]): Theorem[~[A] ->: ~[B]] = t.formula match {
      case a <-> b => assume(~a)(na => iffCommutative(notIff(b))(impliesTransitive(toImplies(iffCommutative(t)), notIff(a)(na))))
    }
    impliesToIffRule(lemma(thm), lemma(iffCommutative(thm)))
  }

  /** `p \/ q` given `p` */
  def orAddRight[P <: Formula, Q <: Formula](thm: Theorem[P], q: Q): Theorem[P \/ Q] = {
    val p = thm.formula
    iffCommutative(orIff(p, q))(
      iffAddNot(iffCommutative(andIff(~p, ~q)))(
        iffCommutative(notIff((~p ->: ~q ->: False) ->: False))(
          toDoubleNegation(swapAssumptions(addAssumption(~q, mixedDoubleNegation(thm))))
        )
      )
    )
  }

  /** `(q -> r) => (p -> r)` given `p => q`. */
  def addConclusion[P <: Formula, Q <: Formula, R <: Formula](pq: Theorem[P ->: Q], r: R): Theorem[(Q ->: R) ->: (P ->: R)] = pq.formula match {
    case p ->: q => assume(q ->: r)(qr => impliesTransitive(pq, qr))
  }

  /** `~q -> ~p` given `p -> q` */
  def impliesInverse[P <: Formula, Q <: Formula](pq: Theorem[P ->: Q]): Theorem[~[Q] ->: ~[P]] = pq.formula match {
    case p ->: q =>
      impliesTransitive(impliesTransitive(toImplies(notIff(q)), addConclusion(pq, False)), toImplies(iffCommutative(notIff(p))))
  }

  /** `~p -> ~q -> false` given `p \/ q` */
  def orImplies[P <: Formula, Q <: Formula](pq: Theorem[P \/ Q]): Theorem[~[P] ->: ~[Q] ->: False] = pq.formula match {
    case p \/ q =>
      assume(~p, ~q)((np, nq) => notIff(~p /\ ~q)(orIff(p, q)(pq))(andCombine(np, nq)))
  }

  /** `r` given `p \/ q`, `p -> r` and `q -> r` */
  def orCase[P <: Formula, Q <: Formula, R <: Formula](pq: Theorem[P \/ Q], pr: Theorem[P ->: R], qr: Theorem[Q ->: R]): Theorem[R] =
    (pq.formula, pr.formula, qr.formula) match {
    case (p \/ q, p1 ->: r, q1 ->: r1) if p == p1 && r == r1 && q == q1 =>
      doubleNegation(r)(impliesTransitive(
        toImplies(iffCommutative(notIff(r))),
        assume(~r)(nr => orImplies(pq)(impliesInverse(pr)(nr))(impliesInverse(qr)(nr)))
      ))
  }

  // --

  def assume[P1 <: Formula, P2 <: Formula, Q <: Formula](p1: P1, p2: P2)(certificate: (Theorem[P1], Theorem[P2]) => Theorem[Q]): Theorem[P1 ->: P2 ->: Q] =
    assume(p1)(t1 => assume(p2)(t2 => certificate(t1, t2)))

  def assume[P1 <: Formula, P2 <: Formula, P3 <: Formula, Q <: Formula](p1: P1, p2: P2, p3: P3)(certificate: (Theorem[P1], Theorem[P2], Theorem[P3]) => Theorem[Q]): Theorem[P1 ->: P2 ->: P3 ->: Q] =
    assume(p1, p2)((t1, t2) => assume(p3)(t3 => certificate(t1, t2, t3)))

  def assume[P1 <: Formula, P2 <: Formula, P3 <: Formula, P4 <: Formula, Q <: Formula](p1: P1, p2: P2, p3: P3, p4: P4)(certificate: (Theorem[P1], Theorem[P2], Theorem[P3], Theorem[P4]) => Theorem[Q]): Theorem[P1 ->: P2 ->: P3 ->: P4 ->: Q] =
    assume(p1, p2, p3)((t1, t2, t3) => assume(p4)(t4 => certificate(t1, t2, t3, t4)))

  def assume[P1 <: Formula, P2 <: Formula, P3 <: Formula, P4 <: Formula, P5 <: Formula, Q <: Formula](p1: P1, p2: P2, p3: P3, p4: P4, p5: P5)(certificate: (Theorem[P1], Theorem[P2], Theorem[P3], Theorem[P4], Theorem[P5]) => Theorem[Q]): Theorem[P1 ->: P2 ->: P3 ->: P4 ->: P5 ->: Q] =
    assume(p1, p2, p3, p4)((t1, t2, t3, t4) => assume(p5)(t5 => certificate(t1, t2, t3, t4, t5)))

  def assume[P1 <: Formula, P2 <: Formula, P3 <: Formula, P4 <: Formula, P5 <: Formula, P6 <: Formula, Q <: Formula](p1: P1, p2: P2, p3: P3, p4: P4, p5: P5, p6: P6)(certificate: (Theorem[P1], Theorem[P2], Theorem[P3], Theorem[P4], Theorem[P5], Theorem[P6]) => Theorem[Q]): Theorem[P1 ->: P2 ->: P3 ->: P4 ->: P5 ->: P6 ->: Q] =
    assume(p1, p2, p3, p4, p5)((t1, t2, t3, t4, t5) => assume(p6)(t6 => certificate(t1, t2, t3, t4, t5, t6)))

}
