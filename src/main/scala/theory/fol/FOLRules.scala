package theory.fol

trait FOLRules extends FOL {

  @deprecated
  def oops[P <: Formula](f: P): Theorem[P] = Theorem(f)

  /** `q` given `p -> q` and `p` */
  def modusPonens[P <: Formula, Q <: Formula](pq: Theorem[P ->: Q], p: Theorem[P]): Theorem[Q] = pq.formula match {
    case p1 ->: q if p.formula == p1 => Theorem(q)
  }

  /** `((p -> false) -> false) -> p` */
  def doubleNegation[P <: Formula](p: P): Theorem[((P ->: False) ->: False) ->: P] =
    Theorem(((p ->: False) ->: False) ->: p)

  /** `(p <-> q) -> p -> q` */
  def iffToImplies1[P <: Formula, Q <: Formula](p: P, q: Q): Theorem[(P <-> Q) ->: P ->: Q] =
    Theorem((p <-> q) ->: p ->: q)

  /** `(p <-> q) -> q -> p` */
  def iffToImplies2[P <: Formula, Q <: Formula](p: P, q: Q): Theorem[(P <-> Q) ->: Q ->: P] =
    Theorem((p <-> q) ->: q ->: p)

  /** `(p -> q) -> (q -> p) -> (p <-> q)` */
  def impliesToIff[P <: Formula, Q <: Formula](p: P, q: Q): Theorem[(P ->: Q) ->: (Q ->: P) ->: (P <-> Q)] =
    Theorem((p ->: q) ->: (q ->: p) ->: (p <-> q))

  /** `true <-> (false -> false)` */
  def trueIff: Theorem[True <-> (False ->: False)] = Theorem(True <-> (False ->: False))

  /** `~p <-> (p -> false)` */
  def notIff[P <: Formula](p: P): Theorem[~[P] <-> (P ->: False)] = Theorem(~p <-> (p ->: False))

  /** `(p /\ q) <-> ((p -> q -> false) -> false)` */
  def andIff[P <: Formula, Q <: Formula](p: P, q: Q): Theorem[(P /\ Q) <-> ((P ->: Q ->: False) ->: False)] =
    Theorem((p /\ q) <-> ((p ->: (q ->: False)) ->: False))

  /** `(p \/ q) <-> (~(~p /\ ~q))` */
  def orIff[P <: Formula, Q <: Formula](p: P, q: Q): Theorem[(P \/ Q) <-> ~[~[P] /\ ~[Q]]] =
    Theorem((p \/ q) <-> ~(~p /\ ~q))

  // --

  /** `p -> q` given `q` in the context of `p` */
  def hypothesis[P <: Formula, Q <: Formula](p: P)(certificate: Theorem[P] => Theorem[Q]): Theorem[P ->: Q] = {
    val q = certificate(Theorem(p)).formula
    Theorem(p ->: q)
  }

  // --

  override def impliesModusPonens[P <: Formula, Q <: Formula](pq: Theorem[P ->: Q], p: Theorem[P]): Theorem[Q] = modusPonens(pq, p)
  override def iffModusPonens[P <: Formula, Q <: Formula](pq: Theorem[P <-> Q], p: Theorem[P]): Theorem[Q] = modusPonens(modusPonens(iffToImplies1(pq.formula.x, pq.formula.y), pq), p)
}
