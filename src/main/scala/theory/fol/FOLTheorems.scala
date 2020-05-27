package theory.fol

import theory.fol.FOL._
import theory.fol.FOLRules._

object FOLTheorems {

  // Modus ponens shorthands
  implicit class WrapperImpliesMP[P <: Formula, Q <: Formula](thm: Theorem[P ->: Q]) {
    def apply(p: Theorem[P]): Theorem[Q] = modusPonens(thm, p)
  }
  implicit class WrapperIffMP[P <: Formula, Q <: Formula](thm: Theorem[P <-> Q]) {
    def apply(p: Theorem[P]): Theorem[Q] = modusPonens(modusPonens(iffToImplies1(thm.formula.x, thm.formula.y), thm), p)
  }

  /** `p -> q -> p` */
  def addImplies[P <: Formula, Q <: Formula](p: P, q: Q): Theorem[P ->: Q ->: P] = assume(p)(tp => assume(q)(_ => tp))

  /** `(p -> q -> r) -> (p -> q) -> (p -> r)` */
  def impliesDistribute[P <: Formula, Q <: Formula, R <: Formula](p: P, q: Q, r: R): Theorem[(P ->: Q ->: R) ->: (P ->: Q) ->: (P ->: R)] =
    assume(p ->: q ->: r)(pqr => assume(p ->: q)(pq => assume(p)(tp => pqr(tp)(pq(tp)))))

  /** `p -> q` given `p <-> q` */
  def toImplies[P <: Formula, Q <: Formula](pq: Theorem[P <-> Q]): Theorem[P ->: Q] = {
    iffToImplies1(pq.formula.x, pq.formula.y)(pq)
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

  /** `true` */
  def truth: Theorem[True] = iffCommutative(trueIff)(assume(False)(identity))

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

  /** `~~p <-> p` */
  def doubleNotIff[P <: Formula](p: P): Theorem[~[~[P]] <-> P] =
    impliesToIffRule(assume(~(~p))(notUnduplicate), assume(p)(notDuplicate))

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

  /** `(q -> r) -> (p -> r)` given `p -> q` */
  def addConclusion[P <: Formula, Q <: Formula, R <: Formula](pq: Theorem[P ->: Q], r: R): Theorem[(Q ->: R) ->: (P ->: R)] = pq.formula match {
    case p ->: q => assume(q ->: r)(qr => impliesTransitive(pq, qr))
  }

  /** `~q -> ~p` given `p -> q` */
  def impliesInverse[P <: Formula, Q <: Formula](pq: Theorem[P ->: Q]): Theorem[~[Q] ->: ~[P]] = pq.formula match {
    case p ->: q =>
      impliesTransitive(impliesTransitive(toImplies(notIff(q)), addConclusion(pq, False)), toImplies(iffCommutative(notIff(p))))
  }

  /** `q -> p` given `~p -> ~q` */
  def impliesUninverse[P <: Formula, Q <: Formula](pq: Theorem[~[P] ->: ~[Q]]): Theorem[Q ->: P] = pq.formula match {
    case ~(p) ->: ~(q) => assume(q)(tq => notUnduplicate(impliesInverse(pq)(notDuplicate(tq))))
  }

  /** `~p -> ~q -> false` given `p \/ q` */
  def orImplies[P <: Formula, Q <: Formula](pq: Theorem[P \/ Q]): Theorem[~[P] ->: ~[Q] ->: False] = pq.formula match {
    case p \/ q =>
      assume(~p, ~q)((np, nq) => notIff(~p /\ ~q)(orIff(p, q)(pq))(andCombine(np, nq)))
  }

  /** `p \/ q` given `~p -> ~q -> false` */
  def impliesOr[P <: Formula, Q <: Formula](pqf: Theorem[~[P] ->: ~[Q] ->: False]): Theorem[P \/ Q] = pqf.formula match {
    case ~(p) ->: ~(q) ->: False =>
      orIff(p, q).swap(#~~(pqf).map(notIff(~p ->: ~q ->: False).swap.toImplies).map(andIff(~p, ~q).toImplies))
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

  /** `p <-> q` given `~p <-> ~q` */
  def iffRemoveNot[P <: Formula, Q <: Formula](thm: Theorem[~[P] <-> ~[Q]]): Theorem[P <-> Q] = thm.formula match {
    case ~(p) <-> ~(q) =>
      val to = assume(p)(tp => mixedDoubleNegationInvert(impliesTransitive(toImplies(iffCommutative(thm)), mixedDoubleNegation(tp))))
      val from = assume(q)(tq => mixedDoubleNegationInvert(impliesTransitive(toImplies(thm), mixedDoubleNegation(tq))))
      impliesToIffRule(to, from)
  }

  /** `~p <-> q` given `p <-> ~q` */
  def iffSwapNot[P <: Formula, Q <: Formula](thm: Theorem[P <-> ~[Q]]): Theorem[~[P] <-> Q] = thm.formula match {
    case p <-> ~(q) =>
      val t = iffAddNot(thm)
      impliesToIffRule(assume(~p)(np => notUnduplicate(t(np))), assume(q)(tq => iffCommutative(t)(notDuplicate(tq))))
  }

  /** `false -> p` */
  def exFalso[P <: Formula](p: P): Theorem[False ->: P] = assume(False)(h => doubleNegation(p)(assume(p ->: False)(_ => h)))

  /** `p <-> q` given `p /\ q` */
  def andToIff[P <: Formula, Q <: Formula](thm: Theorem[P /\ Q]): Theorem[P <-> Q] = thm.formula match {
    case p /\ q =>
      impliesToIffRule(assume(p)(_ => andExtractLeft(andCommutative(thm))), assume(q)(_ => andExtractLeft(thm)))
  }

  /** `((p /\ q) /\ r) <-> (p /\ (q /\ r))` */
  def andAssociativeIff[P <: Formula, Q <: Formula, R <: Formula](p: P, q: Q, r: R): Theorem[((P /\ Q) /\ R) <-> ((P /\ (Q /\ R)))] = {
    val ~> = assume((p /\ q) /\ r) { hyp =>
      val (tpq, tr) = (andExtractLeft(hyp), andExtractLeft(andCommutative(hyp)))
      val (tp, tq) = (andExtractLeft(tpq), andExtractLeft(andCommutative(tpq)))
      andCombine(tp, andCombine(tq, tr))
    }
    val <~ = assume(p /\ (q /\ r)) { hyp =>
      val (tp, tqr) = (andExtractLeft(hyp), andExtractLeft(andCommutative(hyp)))
      val (tq, tr) = (andExtractLeft(tqr), andExtractLeft(andCommutative(tqr)))
      andCombine(andCombine(tp, tq), tr)
    }
    impliesToIffRule(~>, <~)
  }

  /** `~p /\ ~q` given `~(p \/ q)` */
  def notOr[P <: Formula, Q <: Formula](thm: Theorem[~[P \/ Q]]): Theorem[~[P] /\ ~[Q]] = thm.formula match {
    case ~(p \/ q) =>
      iffCommutative(andIff(~p, ~q))(assume(~p ->: ~q ->: False)(h => notIff(p \/ q)(thm)(impliesOr(h))))
  }

  /** `~(p \/ q)` given `~p /\ ~q` */
  def orNot[P <: Formula, Q <: Formula](thm: Theorem[~[P] /\ ~[Q]]): Theorem[~[P \/ Q]] = thm.formula match {
    case ~(p) /\ ~(q) =>
      iffCommutative(notIff(p \/ q))(assume(p \/ q)(h => orImplies(h)(andExtractLeft(thm))(andExtractLeft(andCommutative(thm)))))
  }

  /** `((p \/ q) \/ r) <-> (p \/ (q \/ r))` */
  def orAssociativeIff[P <: Formula, Q <: Formula, R <: Formula](p: P, q: Q, r: R): Theorem[((P \/ Q) \/ R) <-> ((P \/ (Q \/ R)))] = {
    val ~> = assume((p \/ q) \/ r) { hyp =>
      impliesOr(
        assume(~p, ~(q \/ r)) { (tnp, h) =>
          val nqnr = notOr(h)
          impliesTransitive(assume(~p /\ ~q)(orNot), orImplies(hyp))(andCombine(tnp, andExtractLeft(nqnr)))(andExtractLeft(andCommutative(nqnr)))
        }
      )
    }
    val <~ = assume(p \/ (q \/ r)) { hyp =>
      impliesOr(
        assume(~(p \/ q), ~r) { (h1, nr) =>
          val npnq = notOr(h1)
          orImplies(hyp)(andExtractLeft(npnq))(orNot(andCombine(andExtractLeft(andCommutative(npnq)), nr)))
        }
      )
    }

    impliesToIffRule(~>, <~)
  }

  /** `~p \/ ~q` given `~(p /\ q)` */
  def notAnd[P <: Formula, Q <: Formula](thm: Theorem[~[P /\ Q]]): Theorem[~[P] \/ ~[Q]] = thm.formula match {
    case ~(p /\ q) =>
      iffCommutative(orIff(~p, ~q))(
        iffCommutative(notIff(~(~p) /\ ~(~q)))(
          assume(~(~p) /\ ~(~q))(h =>
            notIff(p /\ q)(thm)(andCombine(notUnduplicate(andExtractLeft(h)), notUnduplicate(andExtractLeft(andCommutative(h)))))
          )
        )
      )
  }

  /** `~(p /\ q)` given `~p \/ ~q` */
  def andNot[P <: Formula, Q <: Formula](thm: Theorem[~[P] \/ ~[Q]]): Theorem[~[P /\ Q]] = thm.formula match {
    case ~(p) \/ ~(q) =>
      iffCommutative(notIff(p /\ q))(
        assume(p /\ q)(h =>
          notIff(~(~p) /\ ~(~q))(orIff(~p, ~q)(thm))(andCombine(notDuplicate(andExtractLeft(h)), notDuplicate(andExtractLeft(andCommutative(h)))))
        )
      )
  }

  /** `(p /\ q) <-> ~(~p \/ ~q)` */
  def andIffAlt[P <: Formula, Q <: Formula](p: P, q: Q): Theorem[(P /\ Q) <-> ~[~[P] \/ ~[Q]]] = {
    val ~> = assume(p /\ q) { hyp =>
      iffCommutative(notIff(~p \/ ~q))(impliesTransitive(
        toImplies(orIff(~p, ~q)),
        notIff(~((~(~p) /\ ~(~q))))(iffCommutative(doubleNotIff(~(~p) /\ ~(~q)))(
          andCombine(iffCommutative(doubleNotIff(p))(andExtractLeft(hyp)), iffCommutative(doubleNotIff(q))(andExtractLeft(andCommutative(hyp))))
        ))
      ))
    }
    val <~ = assume(~(~p \/ ~q)) { hyp =>
      val t = notUnduplicate(iffAddNot(orIff(~p, ~q))(hyp))
      andCombine(notUnduplicate(andExtractLeft(t)), notUnduplicate(andExtractLeft(andCommutative(t))))
    }

    impliesToIffRule(~>, <~)
  }

  /** `~p \/ q` given `p -> q` */
  def impliesToOr[P <: Formula, Q <: Formula](thm: Theorem[P ->: Q]): Theorem[~[P] \/ Q] =
    impliesOr(assume(~(~thm.x), ~thm.y) { (nnp, nq) =>
      nq.toImplies(thm(nnp.unduplicate))
    })

  /** `p -> q` given `~p \/ q` */
  def orToImplies[P <: Formula, Q <: Formula](thm: Theorem[~[P] \/ Q]): Theorem[P ->: Q] = {
    val (p, q) = (thm.x.x, thm.y)
    assume(p)(tp => orCase(thm, assume(~p)(np => exFalso(q)(notIff(p)(np)(tp))), assume(q)(identity)))
  }

  /** `~r \/ ~q` given `r -> (p <-> q)` and `~p` */
  def notDefinition[P <: Formula, Q <: Formula, R <: Formula](iff: Theorem[R ->: (P <-> Q)], np: Theorem[~[P]]): Theorem[~[R] \/ ~[Q]] = {
    val (p, q, r) = (np.x, iff.y.y, iff.x)
    impliesOr(assume(~(~r), ~(~q))((nr, nq) => notIff(p)(np)(iffCommutative(iff(notUnduplicate(nr)))(notUnduplicate(nq)))))
  }

  // --

  implicit def theoremToFormula[F <: Formula](thm: Theorem[F]): F = thm.formula

  //implicit def assumptionToFunction[P <: Formula, Q <: Formula](f: Theorem[P ->: Q]): Theorem[P] => Theorem[Q] = p => f(p)

  //implicit def functionToTheorem[P <: Formula, Q <: Formula](f: P => Theorem[Q]): Theorem[P ->: Q] = assume(p)

  def #~~[P <: Formula](thm: Theorem[P]): Theorem[~[~[P]]] = notDuplicate(thm)

  trait WrapperBase[P <: Formula] {
    protected def thm: Theorem[P]
  }

  trait WrapperBinary[F[_ <: Formula, _ <: Formula] <: Formula, P <: Formula, Q <: Formula] extends WrapperBase[F[P, Q]] {
    protected def leftFormula: P
    protected def rightFormula: Q
  }

  trait LeftMappable[F[_ <: Formula, _ <: Formula] <: Formula, P <: Formula, Q <: Formula] extends WrapperBinary[F, P, Q] {
    def mapLeft[M <: Formula](map: Theorem[P ->: M]): Theorem[F[M, Q]]
    final def mapLeft[M <: Formula](f: Theorem[P] => Theorem[M]): Theorem[F[M, Q]] = mapLeft(assume(leftFormula)(f))
  }

  trait RightMappable[F[_ <: Formula, _ <: Formula] <: Formula, P <: Formula, Q <: Formula] extends WrapperBinary[F, P, Q] {
    def mapRight[M <: Formula](map: Theorem[Q ->: M]): Theorem[F[P, M]]
    final def mapRight[M <: Formula](f: Theorem[Q] => Theorem[M]): Theorem[F[P, M]] = mapRight(assume(rightFormula)(f))
  }

  trait EitherMappable[F[_ <: Formula, _ <: Formula] <: Formula, P <: Formula, Q <: Formula] extends LeftMappable[F, P, Q] with RightMappable[F, P, Q]

  trait SymmetricProperty[F[_ <: Formula, _ <: Formula] <: Formula, P <: Formula, Q <: Formula] extends WrapperBinary[F, P, Q] {
    def swap: Theorem[F[Q, P]]
  }

  implicit class WrapperFormula[P <: Formula](f: P) {
    def #\/[Q <: Formula](that: Theorem[Q]): Theorem[P \/ Q] = orCommutative(orAddRight(that, f))
    def #->:[Q <: Formula](that: Theorem[Q]): Theorem[P ->: Q] = assume(f)(_ => that)
    def reflexive: Theorem[P <-> P] = iffReflexive(f)
  }

  implicit class WrapperTheorem[P <: Formula](thm: Theorem[P]) {
    def #\/[Q <: Formula](that: Q): Theorem[P \/ Q] = orAddRight(thm, that)
    def #\/[Q <: Formula](that: Theorem[Q]): Theorem[P \/ Q] = orAddRight(thm, that.formula)
    def #/\[Q <: Formula](that: Theorem[Q]): Theorem[P /\ Q] = andCombine(thm, that)
    def #->:[Q <: Formula](that: Theorem[Q]): Theorem[P ->: Q] = addAssumption(thm.formula, that)
    def #<->[Q <: Formula](that: Theorem[Q]): Theorem[P <-> Q] = andToIff(andCombine(thm, that))
  }

  implicit class WrapperIff[P <: Formula, Q <: Formula](override val thm: Theorem[P <-> Q]) extends SymmetricProperty[<->, P, Q] {
    override protected def leftFormula: P = thm.x
    override protected def rightFormula: Q = thm.y

    def join[R <: Formula](that: Theorem[Q <-> R]): Theorem[P <-> R] = iffTransitive(thm, that)
    override def swap: Theorem[Q <-> P] = iffCommutative(thm)
    def toImplies: Theorem[P ->: Q] = FOLTheorems.this.toImplies(thm)
    def inverse: Theorem[~[P] <-> ~[Q]] = iffAddNot(thm)
  }
  implicit class WrapperIffN[P <: Formula, Q <: Formula](thm: Theorem[P <-> ~[Q]]) {
    def swapNot: Theorem[~[P] <-> Q] = iffSwapNot(thm)
  }
  implicit class WrapperNIff[P <: Formula, Q <: Formula](thm: Theorem[~[P] <-> Q]) {
    def swapNot: Theorem[P <-> ~[Q]] = iffCommutative(iffSwapNot(iffCommutative(thm)))
  }
  implicit class WrapperNIffN[P <: Formula, Q <: Formula](thm: Theorem[~[P] <-> ~[Q]]) {
    def uninverse: Theorem[P <-> Q] = iffRemoveNot(thm)
  }

  implicit def iffToImplies[P <: Formula, Q <: Formula](thm: Theorem[P <-> Q]): Theorem[P ->: Q] = thm.toImplies

  implicit class WrapperImplies[P <: Formula, Q <: Formula](thm: Theorem[P ->: Q]) {
    def join[R <: Formula](that: Theorem[Q ->: R]): Theorem[P ->: R] = impliesTransitive(thm, that)
    def join[R <: Formula](f: Theorem[Q] => Theorem[R]): Theorem[P ->: R] = join(assume(thm.y)(f))
    def inverse: Theorem[~[Q] ->: ~[P]] = impliesInverse(thm)
    def combine(that: Theorem[Q ->: P]): Theorem[P <-> Q] = impliesToIffRule(thm, that)
  }
  implicit class WrapperNImpliesN[P <: Formula, Q <: Formula](thm: Theorem[~[P] ->: ~[Q]]) {
    def uninverse: Theorem[Q ->: P] = impliesUninverse(thm)
  }

  implicit class WrapperAnd[P <: Formula, Q <: Formula](override val thm: Theorem[P /\ Q]) extends EitherMappable[/\, P, Q] with SymmetricProperty[/\, P, Q] {
    override protected def leftFormula: P = thm.x
    override protected def rightFormula: Q = thm.y

    def left: Theorem[P] = andExtractLeft(thm)
    def right: Theorem[Q] = andExtractLeft(andCommutative(thm))
    def asPair: (Theorem[P], Theorem[Q]) = (left, right)
    override def swap: Theorem[Q /\ P] = andCommutative(thm)
    override def mapLeft[M <: Formula](map: Theorem[P ->: M]): Theorem[M /\ Q] = andCombine(map(left), right)
    override def mapRight[M <: Formula](map: Theorem[Q ->: M]): Theorem[P /\ M] = andCombine(left, map(right))
    def toImplies: Theorem[(P ->: Q ->: False) ->: False] = andIff(thm.formula.x, thm.formula.y)(thm)
    def toIff: Theorem[P <-> Q] = andToIff(thm)
  }

  implicit class WrapperAndParen1[P <: Formula, Q <: Formula, R <: Formula](thm: Theorem[(P /\ Q) /\ R]) {
    def rearrange: Theorem[P /\ (Q /\ R)] = andAssociativeIff(thm.x.x, thm.x.y, thm.y)(thm)
  }

  implicit class WrapperAndParen2[P <: Formula, Q <: Formula, R <: Formula](thm: Theorem[P /\ (Q /\ R)]) {
    def rearrange: Theorem[(P /\ Q) /\ R] = andAssociativeIff(thm.x, thm.y.x, thm.y.y).swap(thm)
  }

  implicit class WrapperOr[P <: Formula, Q <: Formula](override val thm: Theorem[P \/ Q]) extends EitherMappable[\/, P, Q] with SymmetricProperty[\/, P, Q] {
    override protected def leftFormula: P = thm.x
    override protected def rightFormula: Q = thm.y

    def left(proof: Theorem[Q ->: False]): Theorem[P] = mixedDoubleNegationInvert(swapAssumptions(orImplies(thm))(iffCommutative(notIff(proof.formula.x))(proof)))
    def right(proof: Theorem[P ->: False]): Theorem[Q] = mixedDoubleNegationInvert(orImplies(thm)(iffCommutative(notIff(proof.formula.x))(proof)))
    override def swap: Theorem[Q \/ P] = orCommutative(thm)
    override def mapLeft[M <: Formula](map: Theorem[P ->: M]): Theorem[M \/ Q] =
      impliesOr(swapAssumptions(swapAssumptions(orImplies(thm)) join assume(~thm.x ->: False)(mixedDoubleNegationInvert) join map join assume(map.y)(mixedDoubleNegation)))
    override def mapRight[M <: Formula](map: Theorem[Q ->: M]): Theorem[P \/ M] =
      impliesOr(orImplies(thm) join assume(~thm.y ->: False)(mixedDoubleNegationInvert) join map join assume(map.y)(mixedDoubleNegation))
    def reduce[R <: Formula](left: Theorem[P ->: R])(right: Theorem[Q ->: R]): Theorem[R] = orCase(thm, left, right)
    def reduce[R <: Formula](leftF: Theorem[P] => Theorem[R])(rightF: Theorem[Q] => Theorem[R]): Theorem[R] = reduce(assume(leftFormula)(leftF))(assume(rightFormula)(rightF))
    //def toImplies: Theorem[(P ->: False) ->: (Q ->: False) ->: False] = ???
    def toImpliesNot: Theorem[~[P] ->: ~[Q] ->: False] = orImplies(thm)
  }

  implicit class WrapperNot[P <: Formula](thm: Theorem[~[P]]) {
    def toImplies: Theorem[P ->: False] = notIff(thm.formula.x)(thm)
    def map[Q <: Formula](map: Theorem[Q ->: P]): Theorem[~[Q]] = map.inverse(thm)
  }

  implicit class WrapperNotNot[P <: Formula](thm: Theorem[~[~[P]]]) {
    def unduplicate: Theorem[P] = notUnduplicate(thm)
  }

  implicit class WrapperImpliesFF[P <: Formula](thm: Theorem[(P ->: False) ->: False]) {
    def unduplicate: Theorem[P] = doubleNegation(thm.x.x)(thm)
  }

  implicit class WrapperImpliesF[P <: Formula](thm: Theorem[P ->: False]) {
    def toNot: Theorem[~[P]] = iffCommutative(notIff(thm.formula.x))(thm)
  }

  implicit class WrapperFalse(thm: Theorem[False]) {
    def apply[P <: Formula](p: P): Theorem[P] = exFalso(p)(thm)
  }

  implicit class WrapperOrImplies[P <: Formula, Q <: Formula](thm: Theorem[~[P] ->: ~[Q] ->: False]) {
    def toOr: Theorem[P \/ Q] = impliesOr(thm)
  }

}
