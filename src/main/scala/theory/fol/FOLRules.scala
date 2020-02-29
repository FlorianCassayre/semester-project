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

  // TODO forall separate

  /** (forall x. y /\ z) <-> ((forall x. y) /\ (forall x. z)) */
  def forallExtract(named: Named, y: Formula, z: Formula): Theorem =
    Theorem(Iff(Forall(named, And(y, z)), And(Forall(named, y), Forall(named, z))))

  /** (forall x. y) /\ (forall x. z)  given forall x. y /\ z */
  def ruleForallExtract(thm: Theorem): Theorem = thm.formula match {
    case Forall(named, And(y, z)) => forallExtract(named, y, z)
  }

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
}
