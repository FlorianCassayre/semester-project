package theory

trait NBGTheorems extends NBGRules {

  /** `(x = y) <-> ((x sube y) /\ (y sube x))` */
  def equalsSubset[X <: AnySet, Y <: AnySet](x: X, y: Y): Theorem[(X === Y) <-> (SubsetEqual[X, Y] /\ SubsetEqual[Y, X])] = {
    val id = fresh()
    val z = SetVariable(id)
    val to = hypothesis(x === y) { xy =>
      andCombine(
        iffCommutative(subsetEqIff(x, y, id))(forall(equalsIff(x, y, id)(xy))(toImplies)),
        iffCommutative(subsetEqIff(y, x, id))(forall(equalsIff(y, x, id)(equalsSymmetric(xy)))(toImplies))
      )
    }
    val from = hypothesis((x sube y) /\ (y sube x)) { sub =>
      val (lhs, rhs) = (subsetEqIff(x, y, id)(andExtractLeft(sub)), subsetEqIff(y, x, id)(andExtractLeft(andCommutative(sub))))
      iffCommutative(equalsIff(x, y, id))(
        forall(forallAnd(lhs, rhs)) { and =>
          impliesToIff(z in x, z in y)(andExtractLeft(and))(andExtractLeft(andCommutative(and)))
        }
      )
    }

    impliesToIff(x === y, (x sube y) /\ (y sube x))(to)(from)
  }

  /** `x = x` */
  def equalsReflexive[X <: AnySet](x: X): Theorem[X === X] = {
    val id = fresh()
    val z = SetVariable(id)
    toImplies(iffCommutative(equalsIff(x, x, id)))(generalize(iffReflexive(z in x), z))
  }

  /** `y = x` given `x = y` */
  def equalsSymmetric[X <: AnySet, Y <: AnySet](thm: Theorem[X === Y]): Theorem[Y === X] = thm.formula match {
    case x === y =>
      val id = fresh()
      iffCommutative(equalsIff(y, x, id))(forall(equalsIff(x, y, id)(thm))(iffCommutative))
  }

  /** `x = z` given `x = y` and `y = z` */
  def equalsTransitive[X <: AnySet, Y <: AnySet, Z <: AnySet](xy: Theorem[X === Y], yz: Theorem[Y === Z]): Theorem[X === Z] = (xy.formula, yz.formula) match {
    case (x === y1, y2 === z) if y1 == y2 =>
      val id = fresh()
      val res = hypothesis(x === y1) { hyp1 =>
        val xAy = equalsIff(x, y1, id)(hyp1)
        hypothesis(y1 === z) { hyp2 =>
          val yAz = equalsIff(y1, z, id)(hyp2)
          val xIz = forall(forallAnd(xAy, yAz))(thm =>
            iffTransitive(andExtractLeft(thm), andExtractLeft(andCommutative(thm)))
          )
          iffCommutative(equalsIff(x, z, id))(xIz)
        }
      }
      res(xy)(yz)
  }


  /** x in y -> M(x) */
  //def inclusionIsSet(x: AnySet, y: AnySet): Theorem = ???


}
