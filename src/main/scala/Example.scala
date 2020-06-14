import Example.a
import printer.PrettyPrinter
import printer.PrettyPrinter.Options
import solver.Tableaux
import theory.fol.FOL._
import theory.fol.FOLRules._
import theory.fol.FOLTheorems._
import theory.NBGTheory._
import theory.NBGRules._
import theory.NBGTheorems._
import theory.number.NumberTheory._
import theory.number.NumberRules._
import theory.number.NumberTheorems._

object Example extends App {

  // Propositional variable declaration
  val (p, q, r) = (Variable["p"], Variable["q"], Variable["r"])

  {
    val _: Variable["p"] = p  // Type is preserved
    //val _: Variable["q"] = p  // <- does not type check!

    // Declaring formulas using the DSL
    val pqf: (p.T /\ q.T) ->: False = (p /\ q) ->: False
    val _: Implies[And[p.T, q.T], False] = pqf  // Alternative type declaration
    // Types are always inferred; it is not required to provide them to local values

    type P = p.T  // Type of any expression can be extracted with `.T`
    val _: P = p  // `P =:= Variable["p"]`

    // Writing proofs

    // A wrapper for formulas `Theorem[Formula]`
    // It can only be derived from axioms or existing theorems
    val thm: Theorem[True] = truth

    // Assumptions
    val _: Theorem[p.T ->: p.T] = assume(p) { tp: Theorem[p.T] => tp }
    // Returns the theorem `(1) ->: (2)`      ^- (1)         (2) -^

    val _: Theorem[p.T ->: q.T ->: r.T ->: True] = assume(p, q, r) { (tp, tq, tr) => truth }
    // Support for chained assumptions

    // Application
    assume(p ->: q, p) { (pq, tp) =>
      val t: Theorem[q.T] = pq(tp)  // Modus ponens rule in `pq.apply(tp)`
      //tp(pq)  // <- does not type check because `tp` is not an implication
      //pq(pq)  // <- does not type check either because `pq` is not of type `p.T`
      t
    }

    // Assume intermediary results
    {
      val dirty: Theorem[p.T] = oops(p)

      assert(dirty.isDirty)  // Theorem is marked as containing unproven branches

      assert(assume(q)(_ => dirty).isDirty)  // All subsequent leaves inherit this marker
    }

    // High-level tree modification
    assume(~(~p) \/ (q /\ (r ->: r))) { t =>
      t
        .mapLeft(_.unduplicate)  // Clear double negation
        .mapRight(_.left)  // Extract left member
    }

    // Directional proof
    val orIff1: Theorem[(p.T \/ q.T) <-> (~[p.T] ->: q.T)] = {
      val ~> = assume(p \/ q)(_.toImpliesNot.join(_.toNot.unduplicate))
      val <~ = assume(~p ->: q)(_.toOrNotLeft.mapLeft(_.unduplicate))
      ~> combine <~
    }

    // Automatic prover

    val orIff = (p \/ q) <-> (~p ->: ~q ->: False)
    Tableaux.prove(orIff) match {
      case Some(thm) => // ...
      case None => throw new IllegalStateException("Could not prove tautology")
    }
  }

  // Set variables
  val (x, y, z) = (SetVariable["x"], SetVariable["y"], SetVariable["z"])

  {
    // Set theory

    val f1 = z in (x union PairSet(y, EmptySet))

    // Printing
    assert(PrettyPrinter.prettifyFormula(f1)(Options(spaces = true)) == "z ∈ x ⋃ {y, Ø}")

    // Skolemization
    val symmetry: Theorem[(x.T === y.T) ->: (y.T === x.T)] = assume(x === y) { h =>  // Example to prove symmetry
      val z = SkolemFunction2[FA, y.T, x.T](y, x)
      val t1 = equalsIff1(x, y, z)(h)
      val t2 = t1.swap
      equalsIff2(y, x)(t2)
    }


    // (see proof examples in `NBGTheorems`)


    // Automatic prover
    assert(Tableaux.prove((x === y) <-> (y === x)).nonEmpty)
    assert(Tableaux.prove((x inter (y union z)) === ((x inter y) union (x inter z))).nonEmpty)
    assert(Tableaux.prove((x diff (x diff y)) === (x inter y)).nonEmpty)
    assert(Tableaux.prove(
      IsSet(x) ->: IsSet(y) ->: ((SingletonSet(y) union (SingletonSet(x) inter -EmptySet)) === (PairSet(x, y) diff EmptySet))
    ).nonEmpty)
  }

  val (a, b, c) = (NumberVariable["a"], NumberVariable["b"], NumberVariable["c"])

  {
    // Number theory

    val _: AnySet = a  // Numbers transparently coerce with sets

    val _ = a * (b + c) === (a * b) + (a * c)

    val two: Succ[Succ[Zero]] = 2  // Convenient conversions

    // Support for (strongly typed) structural induction
    val thm: Theorem[a.T === (Zero + a.T)] = {
      val base = equSym(Zero + Zero, Zero)(mAxiom5(Zero))  // Base case

      val induct = assume(Ind === (Zero + Ind))(inductHyp =>  // Inductive case
        equCongruence3(
          Succ(Zero + Ind), Succ(Ind), Zero + Succ(Ind)
        )(mAxiom2(Ind, Zero + Ind)(inductHyp))(mAxiom6(Zero, Ind))
      )

      type P[V <: Expr] = V === (Zero + V)  // Functor

      mInduction[P, a.T](a === (Zero + a))(base)(induct)  // Call to axiom
    }
  }

}
