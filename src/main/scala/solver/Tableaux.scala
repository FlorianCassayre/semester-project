package solver

import theory.fol.FOL._
import theory.fol.FOLRules._
import theory.fol.FOLTheorems._

object Tableaux {

  def prove[P <: Formula](p: P): Option[Theorem[P]] = {
    // https://en.wikipedia.org/wiki/Method_of_analytic_tableaux

    type AnyTheorem = Theorem[_ <: Formula]

    // Transparent helper types
    type X = Formula
    type Y = Formula

    // Normally a union type between False and True
    type Result = Formula

    def result(f: Result): Boolean = f match {
      case False => false
      case True => true
    }

    def tableaux(facts: Map[Formula, AnyTheorem], thms: Seq[AnyTheorem]): Theorem[Result] = {
      def alphaConsequence[L <: Formula, R <: Formula](and: Theorem[L /\ R]): Theorem[Result] = {
        val (left, right) = and.asPair
        tableaux(facts, left +: right +: thms.tail)
      }
      def betaBranch[L <: Formula, R <: Formula](or: Theorem[L \/ R]): Theorem[Result] = {
        val l = assume(or.x)(t => tableaux(facts, t +: thms.tail))
        val r = assume(or.y)(t => tableaux(facts, t +: thms.tail))
        if(result(l.y) || result(r.y)) {
          truth
        } else {
          or.reduce(l)(r)
        }
      }

      thms match {
        case thm +: tail =>

          thm.formula match {
            case p /\ q => alphaConsequence(thm.as[X /\ Y])
            case p \/ q => betaBranch(thm.as[X \/ Y])
            case p ->: q => betaBranch(impliesToOr(thm.as[X ->: Y]))
            case p <-> q =>
              val t = thm.as[X <-> Y]
              alphaConsequence(t.toImplies #/\ t.swap.toImplies)
            case ~(~(p)) => tableaux(facts, thm.as[~[~[P]]].unduplicate +: tail)
            case ~(f) =>
              f match {
                case p /\ q => betaBranch(notAnd(thm.as[~[X /\ Y]]))
                case p \/ q => alphaConsequence(notOr(thm.as[~[~[X] \/ ~[Y]]]))
                case p ->: q => alphaConsequence(notOr(thm.as[~[X ->: Y]].map(assume(~p \/ q)(h => orToImplies(h)))).mapLeft(_.unduplicate))
                case p <-> q => betaBranch(notAnd(assume((p ->: q) /\ (q ->: p))(h => thm.as[~[X <-> Y]].toImplies(h.left combine h.right)).toNot))
                case False => tableaux(facts, tail)
                case True => thm.as[~[True]].toImplies(truth)
                case atom => facts.get(atom).map(thm.as[~[X]].toImplies.apply).getOrElse(tableaux(facts + (thm.formula -> thm), tail))
              }
            case False => thm.as[False]
            case True => tableaux(facts, tail)
            case atom => facts.get(~atom).map(_.as[~[X]].toImplies.apply(thm)).getOrElse(tableaux(facts + (thm.formula -> thm), tail))
          }

        case _ => truth // No more inputs
      }
    }

    val res = assume(~p)(np => tableaux(Map.empty, Seq(np)))
    if(result(res.y)) {
      None
    } else {
      Some(mixedDoubleNegationInvert(res.as[~[P] ->: False]))
    }
  }
}
