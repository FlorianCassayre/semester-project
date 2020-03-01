package theory.fol

trait FOLRules extends FOL {

  @deprecated
  def oops(f: Formula): Theorem = Theorem(f)

  /** `q` given `p -> q` and `p` */
  def modusPonens(pq: Theorem, p: Theorem): Theorem = pq.formula match {
    case Implies(p1, q) if p.formula == p1 => Theorem(q)
  }

  /** `forall x. p` given `p` */
  def generalize(p: Theorem, x: Named): Theorem = Theorem(Forall(x, p.formula)) // TODO check free?

  /** `p -> q -> p` */
  def addImplies(p: Formula, q: Formula): Theorem = Theorem(p ->: (q ->: p))

  /** `(p -> q -> r) -> (p -> q) -> (p -> r)` */
  def impliesDistribute(p: Formula, q: Formula, r: Formula): Theorem = Theorem((p ->: (q ->: r)) ->: ((p ->: q) ->: (p ->: r)))

  /** `((p -> false) -> false) -> p` */
  def doubleNegation(p: Formula): Theorem = Theorem(((p ->: False) ->: False) ->: p)

  // --

  /** `p -> (forall x. p)` */
  def forallIntro(p: Formula, x: Named): Theorem = Theorem(p ->: Forall(x, p))

  /** `(p <-> q) -> p -> q` */
  def iffToImplies1(p: Formula, q: Formula): Theorem = Theorem((p <-> q) ->: p ->: q)

  /** `(p <-> q) -> q -> p` */
  def iffToImplies2(p: Formula, q: Formula): Theorem = Theorem((p <-> q) ->: q ->: p)

  /** `(p -> q) -> (q -> p) -> (p <-> q)` */
  def impliesToIff(p: Formula, q: Formula): Theorem = Theorem((p ->: q) ->: (q ->: p) ->: (p <-> q))

  /** `true <-> (false -> false)` */
  def trueIff: Theorem = Theorem(True <-> (False ->: False))

  /** `~p <-> (p -> false)` */
  def notIff(p: Formula): Theorem = Theorem(~p <-> (p ->: False))

  /** `(p /\ q) <-> ((p -> q -> false) -> false)` */
  def andIff(p: Formula, q: Formula): Theorem = Theorem((p /\ q) <-> ((p ->: (q ->: False)) ->: False))

  /** `(p \/ q) <-> (~(~p /\ ~q))` */
  def orIff(p: Formula, q: Formula): Theorem = Theorem((p \/ q) <-> ~(~p /\ ~q))

  /** `(exists x. p) <-> ~(forall x. ~q)` */
  def existsIff(p: Formula, x: Named): Theorem = Theorem(Exists(x, p) <-> ~Forall(x, ~p))

  // --

  /** `a => b` given `b` in the context of `a` */
  def hypothesis(a: Formula)(certificate: Theorem => Theorem): Theorem = {
    val b = certificate(Theorem(a)).formula
    Theorem(Implies(a, b))
  }

  /** `forall z. Q(z)` given `forall z. P(z)` and provided `P` returns `Q` */
  def forall(thm: Theorem)(certificate: Theorem => Theorem): Theorem = thm.formula match {
    case Forall(named, p) => Theorem(Forall(named, certificate(Theorem(p)).formula))
  }

  /** `forall x. P(x) /\ Q(x)` given `forall x. P(x)` and `forall x. Q(x)` */
  def forallAnd(tp: Theorem, tq: Theorem): Theorem = (tp.formula, tq.formula) match {
    case (Forall(x1, p), Forall(x2, q)) if x1 == x2 => Theorem(Forall(x1, And(p, q)))
  }
}
