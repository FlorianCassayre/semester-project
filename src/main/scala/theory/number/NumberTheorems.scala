package theory.number

trait NumberTheorems extends NumberRules {

  /** Theorem (a) `a = a` */
  def equRefl[A <: Expr](a: A): Theorem[A === A] = {
    val t1 = mAxiom5(a)
    val t2 = mAxiom1(a + Zero, a, a)
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
      val induct = assume((a + Ind) === (b + Ind)) { inductHyp =>
        val t1 = inductHyp
        val t2 = hyp // Unused here
        val t3 = mAxiom6(a, Ind)
        val t4 = mAxiom6(b, Ind)
        val t5 = t1
        val t6 = mAxiom2(a + Ind, b + Ind)(t5)
        val t7 = equCongruence2(a + Succ(Ind), Succ(a + Ind), Succ(b + Ind))(t3)(t6)
        val t8 = equCongruence3(Succ(b + Ind), a + Succ(Ind), b + Succ(Ind))(t7)(t4)
        t8
      }

      type P[V <: Expr] = (A + V) === (B + V)

      mInduction[P, C]((a + c) === (b + c))(base)(induct)
    }
  }

  /** Theorem (f) `a = 0 + a` */
  def addIdentityLeft[A <: Expr](a: A): Theorem[A === (Zero + A)] = {
    val base = {
      val t1 = equSym(Zero + Zero, Zero)(mAxiom5(Zero))
      t1
    }
    val induct = assume(Ind === (Zero + Ind)) { inductHyp =>
      val t1 = inductHyp
      val t2 = mAxiom6(Zero, Ind)
      val t3 = mAxiom2(Ind, Zero + Ind)(t1)
      val t4 = equCongruence3(Succ(Zero + Ind), Succ(Ind), Zero + Succ(Ind))(t3)(t2)
      t4
    }

    type P[V <: Expr] = V === (Zero + V)

    val tt: Theorem[P[Ind] ->: P[Succ[Ind]]] = induct

    mInduction[P, A](a === (Zero + a))(base)(induct)
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
    val induct = assume((Succ(a) + Ind) === Succ(a + Ind)) { inductHyp =>
      val t1 = inductHyp
      val t2 = mAxiom6(Succ(a), Ind)
      val t3 = mAxiom2(Succ(a) + Ind, Succ(a + Ind))(t1)
      val t4 = equCongruence2(Succ(a) + Succ(Ind), Succ(Succ(a) + Ind), Succ(Succ(a + Ind)))(t2)(t3)
      val t5 = mAxiom6(a, Ind)
      val t6 = mAxiom2(Plus(a, Succ(Ind)), Succ(a + Ind))(t5)
      val t7 = equCongruence3(Succ(Succ(a + Ind)), Succ(a) + Succ(Ind), Succ(a + Succ(Ind)))(t4)(t6)
      t7
    }

    type P[V <: Expr] = (Succ[A] + V) === Succ[A + V]

    mInduction[P, B](Plus(Succ(a), b) === Succ(a + b))(base)(induct)
  }

  /** Theorem (h) `a + b = b + a` */
  def addCommutative[A <: Expr, B <: Expr](a: A, b: B): Theorem[(A + B) === (B + A)] = {
    val base = {
      val t1 = mAxiom5(a)
      val t2 = addIdentityLeft(a)
      val t3 = equCongruence2(a + Zero, a, Zero + a)(t1)(t2)
      t3
    }
    val (ab, ba) = (a + Ind, Ind + a)
    val induct = assume(ab === ba) { inductHyp =>
      val t1 = inductHyp
      val t2 = mAxiom6(a, Ind)
      val t3 = addSuccLeft(Ind, a)
      val t4 = mAxiom2(ab, ba)(t1)
      val t5 = equCongruence2(a + Succ(Ind), Succ(ab), Succ(ba))(t2)(t4)
      val t6 = equCongruence3(Succ(ba), a + Succ(Ind), Succ(Ind) + a)(t5)(t3)
      t6
    }

    type P[V <: Expr] = (A + V) === (V + A)

    mInduction[P, B]((a + b) === (b + a))(base)(induct)
  }

  /** Theorem (i) `a = b => c + a = c + b` */
  def addLeft[A <: Expr, B <: Expr, C <: Expr](a: A, b: B, c: C): Theorem[(A === B) ->: ((C + A) === (C + B))] = {
    assume(Equals(a, b)) { hyp =>
      val t1 = addRight(a, b, c)
      val t2 = addCommutative(a, c)
      val t3 = addCommutative(b, c)
      val t4 = hyp
      val t5 = t1(t4)
      val t6 = mAxiom1(a + c, c + a, b + c)(t2)(t5)
      val t7 = equCongruence2(c + a, b + c, c + b)(t6)(t3)
      t7
    }
  }

  /** Theorem (j) `(a + b) + c = a + (b + c)` */
  def addAssociative[A <: Expr, B <: Expr, C <: Expr](a: A, b: B, c: C): Theorem[((A + B) + C) === (A + (B + C))] = {
    val base = {
      val t1 = mAxiom5(a + b)
      val t2 = mAxiom5(b)
      val t3 = addLeft(b + Zero, b, a)(t2) // Note: literature contains a typo, it should be read "(i)" instead of "(j)"
      val t4 = equCongruence3(a + b, (a + b) + Zero, a + (b + Zero))(t1)(t3)
      t4
    }
    val induct = assume(((a + b) + Ind) === (a + (b + Ind))) { inductHyp =>
      val t1 = inductHyp
      val t2 = mAxiom6(a + b, Ind)
      val t3 = mAxiom2((a + b) + Ind, a + (b + Ind))(t1)
      val t4 = equCongruence2((a + b) + Succ(Ind), Succ((a + b) + Ind), Succ(a + (b + Ind)))(t2)(t3)
      val t5 = mAxiom6(b, Ind)
      val t6 = addLeft(b + Succ(Ind), Succ(b + Ind), a)(t5)
      val t7 = mAxiom6(a, b + Ind)
      val t8 = equCongruence2(a + (b + Succ(Ind)), a + Succ(b + Ind), Succ(a + (b + Ind)))(t6)(t7)
      val t9 = equCongruence3(Succ(a + (b + Ind)), (a + b) + Succ(Ind), a + (b + Succ(Ind)))(t4)(t8)
      t9
    }

    type P[V <: Expr] = ((A + B) + V) === (A + (B + V))

    mInduction[P, C](((a + b) + c) === (a + (b + c)))(base)(induct)
  }

  /** Theorem (k) `a = b => a * c = b * c` */
  def timesRight[A <: Expr, B <: Expr, C <: Expr](a: A, b: B, c: C): Theorem[(A === B) ->: ((A x C) === (B x C))] = {
    assume(a === b) { hyp =>
      val base = {
        val t1 = mAxiom7(a)
        val t2 = mAxiom7(b)
        val t3 = equSym(b * Zero, Zero)(t2)
        val t4 = equCongruence2(a * Zero, Zero, b * Zero)(t1)(t3)
        t4
      }
      val induct = assume((a * Ind) === (b * Ind)) { inductHyp =>
        val t1 = mAxiom8(a, Ind)
        val t2 = addRight(a * Ind, b * Ind, a)(inductHyp)
        val t3 = addLeft(a, b, b * Ind)(hyp)
        val t4 = equCongruence2((a * Ind) + a, (b * Ind) + a, (b * Ind) + b)(t2)(t3)
        val t5 = equCongruence2(a * Succ(Ind), (a * Ind) + a, (b * Ind) + b)(t1)(t4)
        val t6 = mAxiom8(b, Ind)
        val t7 = equCongruence3((b * Ind) + b, a * Succ(Ind), b * Succ(Ind))(t5)(t6)
        t7
      }

      type P[V <: Expr] = (A x V) === (B x V)

      mInduction[P, C]((a * c) === (b * c))(base)(induct)
    }
  }

  /** Theorem (l) `0 * a = 0` */
  def timesNullLeft[A <: Expr](a: A): Theorem[(Zero x A) === Zero] = {
    val base = {
      val t1 = mAxiom7(Zero)
      t1
    }
    val induct = assume((Zero * Ind) === Zero) { inductHyp =>
      val t1 = mAxiom8(Zero, Ind)
      val t2 = mAxiom5(Zero * Ind)
      val t3 = equCongruence2(Zero * Succ(Ind), (Zero * Ind) + Zero, Zero * Ind)(t1)(t2)
      val t4 = equCongruence2(Zero * Succ(Ind), Zero * Ind, Zero)(t3)(inductHyp)
      t4
    }

    type P[V <: Expr] = (Zero x V) === Zero

    mInduction[P, A]((Zero * a) === Zero)(base)(induct)
  }

  /** Theorem (m) `a' * b = (a * b) + b` */
  def timesSuccLeft[A <: Expr, B <: Expr](a: A, b: B): Theorem[(Succ[A] x B) === ((A x B) + B)] = {
    val base = {
      val t1 = mAxiom7(Succ(a))
      val t2 = mAxiom7(a)
      val t3 = equCongruence3(Zero, Succ(a) * Zero, a * Zero)(t1)(t2)
      val t4 = mAxiom5(a * Zero)
      val t5 = equCongruence3(a * Zero, Succ(a) * Zero, (a * Zero) + Zero)(t3)(t4)
      t5
    }
    val induct = assume((Succ(a) * Ind) === ((a * Ind) + Ind)) { inductHyp =>
      val t1 = mAxiom8(Succ(a), Ind)
      val t2 = addRight(Succ(a) * Ind, (a * Ind) + Ind, Succ(a))(inductHyp)
      val t3 = addAssociative(a * Ind, Ind, Succ(a))
      val t4 = mAxiom6(Ind, a)
      val t5 = addSuccLeft(Ind, a)
      val t6 = equCongruence3(Succ(Ind + a), Ind + Succ(a), Succ(Ind) + a)(t4)(t5)
      val t7 = addCommutative(Succ(Ind), a)
      val t8 = equCongruence2(Ind + Succ(a), Succ(Ind) + a, a + Succ(Ind))(t6)(t7)
      val t9 = addLeft(Ind + Succ(a), a + Succ(Ind), a * Ind)(t8)
      val t10 = equCongruence2(((a * Ind) + Ind) + Succ(a), (a * Ind) + (Ind + Succ(a)), (a * Ind) + (a + Succ(Ind)))(t3)(t9)
      val t11 = addAssociative(a * Ind, a, Succ(Ind))
      val t12 = equCongruence3((a * Ind) + (a + Succ(Ind)), ((a * Ind) + Ind) + Succ(a), ((a * Ind) + a) + Succ(Ind))(t10)(t11)
      val t13 = mAxiom8(a, Ind)
      val t14 = addRight(a * Succ(Ind), (a * Ind) + a, Succ(Ind))(t13)
      val t15 = equCongruence3(((a * Ind) + a) + Succ(Ind), ((a * Ind) + Ind) + Succ(a), (a * Succ(Ind)) + Succ(Ind))(t12)(t14)
      val t16 = equCongruence2((Succ(a) * Ind) + Succ(a), ((a * Ind) + Ind) + Succ(a), (a * Succ(Ind)) + Succ(Ind))(t2)(t15)
      val t17 = equCongruence2(Succ(a) * Succ(Ind), (Succ(a) * Ind) + Succ(a), (a * Succ(Ind)) + Succ(Ind))(t1)(t16)
      t17
    }

    type P[V <: Expr] = (Succ[A] x V) === ((A x V) + V)

    mInduction[P, B]((Succ(a) * b) === ((a * b) + b))(base)(induct)
  }

  /** Theorem (n) `a * b = b * a` */
  def timesCommutative[A <: Expr, B <: Expr](a: A, b: B): Theorem[(A x B) === (B x A)] = {
    lazy val base = {
      val t1 = timesNullLeft(b)
      val t2 = mAxiom7(b)
      val t3 = equCongruence3(Zero, Zero * b, b * Zero)(t1)(t2)
      t3
    }
    val induct = assume((Ind * b) === (b * Ind)) { inductHyp =>
      val t1 = timesSuccLeft(Ind, b)
      val t2 = addRight(Ind * b, b * Ind, b)(inductHyp)
      val t3 = equCongruence2(Succ(Ind) * b, (Ind * b) + b, (b * Ind) + b)(t1)(t2)
      val t4 = mAxiom8(b, Ind)
      val t5 = equCongruence3((b * Ind) + b, Succ(Ind) * b, b * Succ(Ind))(t3)(t4)
      t5
    }

    type P[V <: Expr] = (V x B) === (B x V)

    mInduction[P, A]((a * b) === (b * a))(base)(induct)
  }

  /** Theorem (o) `a = b => c * a = c * b` */
  def timesLeft[A <: Expr, B <: Expr, C <: Expr](a: A, b: B, c: C): Theorem[(A === B) ->: ((C x A) === (C x B))] = {
    assume(a === b) { hyp =>
      val t1 = timesRight(a, b, c)(hyp)
      val t2 = timesCommutative(a, c)
      val t3 = mAxiom1(a * c, b * c, c * a)(t1)(t2)
      val t4 = timesCommutative(b, c)
      val t5 = mAxiom1(b * c, c * a, c * b)(t3)(t4)
      t5
    }
  }

  /** Theorem (a) `a * (b + c) = (a * b) + (a * c)` */
  def rightDistributivity[A <: Expr, B <: Expr, C <: Expr](a: A, b: B, c: C): Theorem[(A x (B + C)) === ((A x B) + (A x C))] = {
    val base = {
      val t1 = mAxiom5(b)
      val t2 = timesLeft(b + Zero, b, a)(t1)
      val t3 = mAxiom7(a)
      val t4 = mAxiom5(a * b)
      val t5 = equCongruence3(a * b, a * (b + Zero), (a * b) + Zero)(t2)(t4)
      val t6 = addLeft(a * Zero, Zero, a * b)(t3)
      val t7 = equCongruence3((a * b) + Zero, a * (b + Zero), (a * b) + (a * Zero))(t5)(t6)
      t7
    }
    val induct = assume((a * (b + Ind)) === ((a * b) + (a * Ind))) { inductHyp =>
      val t1 = mAxiom6(b, Ind)
      val t2 = timesLeft(b + Succ(Ind), Succ(b + Ind), a)(t1)
      val t3 = mAxiom8(a, b + Ind)
      val t4 = equCongruence2(a * (b + Succ(Ind)), a * Succ((b + Ind)), (a * (b + Ind)) + a)(t2)(t3)
      val t5 = addRight(a * (b + Ind), (a * b) + (a * Ind), a)(inductHyp)
      val t6 = addAssociative(a * b, a * Ind, a)
      val t7 = equCongruence2((a * (b + Ind)) + a, ((a * b) + (a * Ind)) + a, (a * b) + ((a * Ind) + a))(t5)(t6)
      val t8 = mAxiom8(a, Ind)
      val t9 = addLeft((a * Ind) + a, a * Succ(Ind), a * b)(equSym(a * Succ(Ind), (a * Ind) + a)(t8))
      val t10 = equCongruence2((a * (b + Ind)) + a, (a * b) + ((a * Ind) + a), (a * b) + (a * Succ(Ind)))(t7)(t9)
      val t11 = equCongruence2(a * (b + Succ(Ind)), (a * (b + Ind)) + a, (a * b) + (a * Succ(Ind)))(t4)(t10)
      t11
    }

    type P[V <: Expr] = (A x (B + V)) === ((A x B) + (A x V))

    mInduction[P, C]((a * (b + c)) === ((a * b) + (a * c)))(base)(induct)
  }

  /** Theorem (b) `(a + b) * c = (a * c) + (b * c)` */
  def leftDistributivity[A <: Expr, B <: Expr, C <: Expr](a: A, b: B, c: C): Theorem[((A + B) x C) === ((A x C) + (B x C))] = {
    val t1 = timesCommutative(c, a + b)
    val t2 = rightDistributivity(c, a, b)
    val t3 = mAxiom1(c * (a + b), (a + b) * c, (c * a) + (c * b))(t1)(t2)
    val t4 = timesCommutative(c, a)
    val t5 = timesCommutative(c, b)
    val t6 = addRight(c * a, a * c, b * c)(t4)
    val t7 = addLeft(c * b, b * c, c * a)(t5)
    val t8 = equCongruence2((a + b) * c, (c * a) + (c * b), (c * a) + (b * c))(t3)(t7)
    val t9 = equCongruence2((a + b) * c, (c * a) + (b * c), (a * c) + (b * c))(t8)(t6)
    t9
  }

  /** Theorem (c) `(a * b) * c = a * (b * c)` */
  def timesAssociative[A <: Expr, B <: Expr, C <: Expr](a: A, b: B, c: C): Theorem[((A x B) x C) === (A x (B x C))] = {
    val base = {
      val t1 = mAxiom7(a * b)
      val t2 = mAxiom7(b)
      val t3 = equCongruence3(Zero, (a * b) * Zero, b * Zero)(t1)(t2)
      val t4 = equCongruence2((a * b) * Zero, b * Zero, Zero)(t3)(t2)
      val t5 = timesLeft(b * Zero, Zero, a)(t2)
      val t6 = mAxiom7(a)
      val t7 = equCongruence2(a * (b * Zero), a * Zero, Zero)(t5)(t6)
      val t8 = equCongruence3(Zero, (a * b) * Zero, a * (b * Zero))(t4)(t7)
      t8
    }
    val induct = assume(((a * b) * Ind) === (a * (b * Ind))) { inductHyp =>
      val t1 = mAxiom8(a * b, Ind)
      val t2 = addRight((a * b) * Ind, a * (b * Ind), a * b)(inductHyp)
      val t3 = equCongruence2((a * b) * Succ(Ind), ((a * b) * Ind) + (a * b), (a * (b * Ind)) + (a * b))(t1)(t2)
      val t4 = rightDistributivity(a, b * Ind, b)
      val t5 = equCongruence3((a * (b * Ind)) + (a * b), (a * b) * Succ(Ind), a * ((b * Ind) + b))(t3)(t4)
      val t6 = mAxiom8(b, Ind)
      val t7 = timesLeft(b * Succ(Ind), (b * Ind) + b, a)(t6)
      val t8 = equCongruence3((a * ((b * Ind) + b)), (a * b) * Succ(Ind), a * (b * Succ(Ind)))(t5)(t7)
      t8
    }

    type P[V <: Expr] = ((A x B) x V) === (A x (B x V))

    mInduction[P, C](((a * b) * c) === (a * (b * c)))(base)(induct)
  }

  /** Theorem (d) `a + c = b + c => a = b` */
  def addCancel[A <: Expr, B <: Expr, C <: Expr](a: A, b: B, c: C): Theorem[((A + C) === (B + C)) ->: (A === B)] = {
    val base = assume((a + Zero) === (b + Zero)) { hyp =>
      val t1 = mAxiom5(a)
      val t2 = mAxiom5(b)
      val t3 = mAxiom1(a + Zero, b + Zero, a)(hyp)(t1)
      val t4 = mAxiom1(b + Zero, a, b)(t3)(t2)
      t4
    }
    val induct = assume(((a + Ind) === (b + Ind)) ->: (a === b), (a + Succ(Ind)) === (b + Succ(Ind))) { (inductHyp, hyp) =>
      val t1 = mAxiom6(a, Ind)
      val t2 = mAxiom6(b, Ind)
      val t3 = mAxiom1(a + Succ(Ind), Succ(a + Ind), b + Succ(Ind))(t1)(hyp)
      val t4 = equCongruence2(Succ(a + Ind), b + Succ(Ind), Succ(b + Ind))(t3)(t2)
      val t5 = mAxiom4(a + Ind, b + Ind)(t4)
      val t6 = inductHyp(t5)
      t6
    }

    type P[V <: Expr] = ((A + V) === (B + V)) ->: (A === B)

    mInduction[P, C](((a + c) === (b + c)) ->: (a === b))(base)(induct)
  }

  /* == Theorems 3.5 == */

  /** Theorem (a) `a + 1 = a'` */
  def addOne[A <: Expr](a: A): Theorem[(A + Succ[Zero]) === Succ[A]] = {
    val t1 = mAxiom6(a, Zero)
    val t2 = mAxiom5(a)
    val t3 = mAxiom2(a + Zero, a)(t2)
    val t4 = equCongruence2(a + Succ(Zero), Succ(a + Zero), Succ(a))(t1)(t3)
    t4
  }

  /** Theorem (b) `a * 1 = a` */
  def timesIdentity[A <: Expr](a: A): Theorem[(A x Succ[Zero]) === A] = {
    val t1 = mAxiom8(a, Zero)
    val t2 = mAxiom7(a)
    val t3 = addRight(a * Zero, Zero, a)(t2)
    val t4 = equCongruence2(a * Succ(Zero), (a * Zero) + a, Zero + a)(t1)(t3)
    val t5 = equSym(a, Zero + a)(addIdentityLeft(a))
    val t6 = equCongruence2(a * Succ(Zero), Zero + a, a)(t4)(t5)
    t6
  }

  /** Theorem (c) `a * 2 = a + a` */
  def timesTwo[A <: Expr](a: A): Theorem[(A x Succ[Succ[Zero]]) === (A + A)] = {
    val t1 = mAxiom8(a, Succ(Zero))
    val t2 = timesIdentity(a)
    val t3 = addRight(a * Succ(Zero), a, a)(t2)
    val t4 = equCongruence2(a * Succ(Succ(Zero)), (a * Succ(Zero)) + a, a + a)(t1)(t3)
    t4
  }

}
