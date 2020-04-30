package theory.number

trait NumberTheorems extends NumberRules {

  /** Theorem (a) `a = a` */
  def equRefl[A <: Expr](a: A): Theorem[A === A] = {
    val t1 = mAxiom5(a)
    val t2 = mAxiom1(Plus(a, Zero), a, a)
    val t3 = t2(t1)
    val t4 = t3(t1)
    t4
  }

  /** Theorem (b) `a = b => b = a` */
  def equSym[A <: Expr, B <: Expr](a: A, b: B): Theorem[(A === B) ->: (B === A)] = {
    val t1 = mAxiom1(a, b, a)
    val t2 = swapAssumptions(t1)
    val t3 = t2(equRefl(a))
    t3
  }

  def equSymRule[A <: Expr, B <: Expr](thm: Theorem[A === B]): Theorem[B === A] = thm.formula match {
    case Equals(a, b) => equSym(a, b)(thm)
  }

  /** Theorem (c) `a = b => (b = c => a = c)` */
  def equCongruence2[A <: Expr, B <: Expr, C <: Expr](a: A, b: B, c: C): Theorem[(A === B) ->: (B === C) ->: (A === C)] = {
    val t1 = mAxiom1(b, a, c)
    val t2 = equSym(a, b)
    val t3 = t2 join t1
    t3
  }

  /** Theorem (d) `b = a => (c = a => b = c)` */
  def equCongruence3[A <: Expr, B <: Expr, C <: Expr](a: A, b: B, c: C): Theorem[(B === A) ->: (C === A) ->: (B === C)] = {
    val t1 = equCongruence2(b, a, c)
    val t2 = swapAssumptions(t1)
    val t3 = equSym(c, a)
    val t4 = swapAssumptions(t3 join t2)
    t4
  }

  /** Theorem (e) `a = b => a + c = b + c` */
  def addRight[A <: Expr, B <: Expr, C <: Expr](a: A, b: B, c: C): Theorem[(A === B) ->: ((A + C) === (B + C))] = {
    assume(a === b) { hyp =>
      val base = {
        val t1 = mAxiom5(a)
        val t2 = mAxiom5(b)
        val t3 = hyp
        val t4 = equCongruence2(a + Zero, a, b)(t1)(t3)
        val t5 = equCongruence3(b, a + Zero, b + Zero)(t4)(t2)
        t5
      }
      val v = Ind
      val induct = assume((a + v) === (b + v)) { inductHyp =>
        val t1 = inductHyp
        val t2 = hyp // Unused here
        val t3 = mAxiom6(a, v)
        val t4 = mAxiom6(b, v)
        val t5 = t1
        val t6 = mAxiom2(a + v, b + v)(t5)
        val t7 = equCongruence2(a + Succ(v), Succ(a + v), Succ(b + v))(t3)(t6)
        val t8 = equCongruence3(Succ(b + v), a + Succ(v), b + Succ(v))(t7)(t4)
        t8
      }

      type P[V <: Expr] = (A + V) === (B + V)

      mInduction[P, C]((a + c) === (b + c))(base)(induct)
    }
  }

  /** Theorem (g) `a' + b = (a + b)'` */
  def addSuccLeft[A <: Expr, B <: Expr](a: A, b: B): Theorem[(Succ[A] + B) === Succ[A + B]] = {
    val base = {
      val t1 = mAxiom5(Succ(a))
      val t2 = mAxiom5(a)
      val t3 = mAxiom2(a + Zero, a)(t2)
      val t4 = equCongruence3(Succ(a), Succ(a) + Zero, Succ(a + Zero))(t1)(t3)
      t4
    }
    val d = Ind
    val induct = assume((Succ(a) + d) === Succ(a + d)) { inductHyp =>
      val t1 = inductHyp
      val t2 = mAxiom6(Succ(a), d)
      val t3 = mAxiom2(Succ(a) + d, Succ(a + d))(t1)
      val t4 = equCongruence2(Succ(a) + Succ(d), Succ(Succ(a) + d), Succ(Succ(a + d)))(t2)(t3)
      val t5 = mAxiom6(a, d)
      val t6 = mAxiom2(Plus(a, Succ(d)), Succ(a + d))(t5)
      val t7 = equCongruence3(Succ(Succ(a + d)), Succ(a) + Succ(d), Succ(a + Succ(d)))(t4)(t6)
      t7
    }

    type P[V <: Expr] = (Succ[A] + V) === Succ[A + V]

    mInduction[P, B](Plus(Succ(a), b) === Succ(Plus(a, b)))(base)(induct)
  }

}
