package theory.number

trait NumberRules extends NumberTheory {

  /** `0 = {}` */
  def zeroIff: Theorem[Zero === EmptySet] = Axiom(Zero === EmptySet)

  /** `S(n) = (n union {n})` */
  def successorIff[N <: Expr](n: N): Theorem[Succ[N] === Union[N, SingletonSet[N]]] = Axiom(Succ(n) === (n union SingletonSet(n)))


  /** `(a = b) -> (a = c) -> (b = c)` */
  def mAxiom1[A <: Expr, B <: Expr, C <: Expr](a: A, b: B, c: C): Theorem[(A === B) ->: (A === C) ->: (B === C)] =
    assume(a === b, a === c)((ab, ac) => ab.swap join ac)

  /** `(a = b) -> (a' = b')` */
  def mAxiom2[A <: Expr, B <: Expr](a: A, b: B): Theorem[(A === B) ->: (Succ[A] === Succ[B])] = Axiom((a === b) ->: (Succ(a) === Succ(b))) // TODO

  /** `~(0 = a')` */
  def mAxiom3[A <: Expr](a: A): Theorem[~[Zero === Succ[A]]] = Axiom(~(Zero === Succ(a))) // TODO

  /** `(a' = b') -> (a = b)` */
  def mAxiom4[A <: Expr, B <: Expr](a: A, b: B): Theorem[(Succ[A] === Succ[B]) ->: (A === B)] = Axiom((Succ(a) === Succ(b)) ->: (a === b)) // TODO

  /** `a + 0 = a` */
  def mAxiom5[A <: Expr](a: A): Theorem[(A + Zero) === A] = Axiom((a + Zero) === a) // TODO

  /** `a + b' = (a + b)'` */
  def mAxiom6[A <: Expr, B <: Expr](a: A, b: B): Theorem[(A + Succ[B]) === Succ[A + B]] = Axiom((a + Succ(b) === Succ(a + b))) // TODO

  /** `a * 0 = 0` */
  def mAxiom7[A <: Expr](a: A): Theorem[(A x Zero) === Zero] = Axiom((a * Zero) === Zero) // TODO

  /** `a * b' = (a * b) + a` */
  def mAxiom8[A <: Expr, B <: Expr](a: A, b: B): Theorem[(A x B) === ((A x B) + A)] = Axiom((a * b) === ((a * b) + a)) // TODO


  def mInduction[P[N <: Expr] <: Formula, R <: Expr](p: P[R])(base: Theorem[P[Zero]])(inductive: Theorem[P[Ind] ->: P[Succ[Ind]]]):
  Theorem[P[R]] = Axiom(p) // TODO
}
