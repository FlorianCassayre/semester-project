package theory.fol

import java.util.concurrent.atomic.AtomicBoolean

import theory.fol.FOL._

object FOLRules {

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
