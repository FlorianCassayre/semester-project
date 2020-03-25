package theory.fol

import java.util.concurrent.atomic.AtomicBoolean

trait FOLRules extends FOL {

  @deprecated
  def oops[P <: Formula](f: P): Theorem[P] = Axiom(f, dirty = true)

  /** `q` given `p -> q` and `p` */
  def modusPonens[P <: Formula, Q <: Formula](pq: Theorem[P ->: Q], p: Theorem[P]): Theorem[Q] = pq.formula match {
    case p1 ->: q if p.formula == p1 => Axiom(q, Set[Theorem[_]](pq, p))
  }

  /** `((p -> false) -> false) -> p` */
  def doubleNegation[P <: Formula](p: P): Theorem[((P ->: False) ->: False) ->: P] =
    Axiom(((p ->: False) ->: False) ->: p)

  /** `(p <-> q) -> p -> q` */
  def iffToImplies1[P <: Formula, Q <: Formula](p: P, q: Q): Theorem[(P <-> Q) ->: P ->: Q] =
    Axiom((p <-> q) ->: p ->: q)

  /** `(p <-> q) -> q -> p` */
  def iffToImplies2[P <: Formula, Q <: Formula](p: P, q: Q): Theorem[(P <-> Q) ->: Q ->: P] =
    Axiom((p <-> q) ->: q ->: p)

  /** `(p -> q) -> (q -> p) -> (p <-> q)` */
  def impliesToIff[P <: Formula, Q <: Formula](p: P, q: Q): Theorem[(P ->: Q) ->: (Q ->: P) ->: (P <-> Q)] =
    Axiom((p ->: q) ->: (q ->: p) ->: (p <-> q))

  /** `true <-> (false -> false)` */
  def trueIff: Theorem[True <-> (False ->: False)] = Axiom(True <-> (False ->: False))

  /** `~p <-> (p -> false)` */
  def notIff[P <: Formula](p: P): Theorem[~[P] <-> (P ->: False)] = Axiom(~p <-> (p ->: False))

  /** `(p /\ q) <-> ((p -> q -> false) -> false)` */
  def andIff[P <: Formula, Q <: Formula](p: P, q: Q): Theorem[(P /\ Q) <-> ((P ->: Q ->: False) ->: False)] =
    Axiom((p /\ q) <-> ((p ->: (q ->: False)) ->: False))

  /** `(p \/ q) <-> (~(~p /\ ~q))` */
  def orIff[P <: Formula, Q <: Formula](p: P, q: Q): Theorem[(P \/ Q) <-> ~[~[P] /\ ~[Q]]] =
    Axiom((p \/ q) <-> ~(~p /\ ~q))

  // --

  /** `p -> q` given `q` in the context of `p` */
  def assume[P <: Formula, Q <: Formula](p: P)(certificate: Theorem[P] => Theorem[Q]): Theorem[P ->: Q] = {
    val ref = new AtomicBoolean()
    val ret = certificate(Axiom(p, dirty = false, Set(ref)))
    val q = ret.formula
    val newRefs = ret.context.invalid - ref
    val dirty = ret.isDirty
    ref.set(true)
    Axiom(p ->: q, dirty, newRefs)
  }

  // --

  override def impliesModusPonens[P <: Formula, Q <: Formula](pq: Theorem[P ->: Q], p: Theorem[P]): Theorem[Q] = modusPonens(pq, p)
  override def iffModusPonens[P <: Formula, Q <: Formula](pq: Theorem[P <-> Q], p: Theorem[P]): Theorem[Q] = modusPonens(modusPonens(iffToImplies1(pq.formula.x, pq.formula.y), pq), p)
}
