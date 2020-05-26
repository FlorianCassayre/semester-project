import theory.fol.FOL._
import solver.Tableaux._

class TestTableaux extends ProofTestSuite {

  private val binary: Seq[(Formula, Formula) => Formula] =
    Seq(_ /\ _, _ \/ _, _ ->: _, _ <-> _)
  private val unary: Seq[Formula => Formula] =
    Seq(~_)
  private val constant: Seq[Formula] =
    Seq(False, True)
  private def variable(i: Int): Formula = {
    require(i >= 0)
    Variable("v" + i.toString)
  }

  private def isTautology(f: Formula): Boolean = {
    type AnyVariable = Variable[_ <: String]

    def getVariables(f: Formula): Set[AnyVariable] = f match {
      case p /\ q => getVariables(p) ++ getVariables(q)
      case p \/ q => getVariables(p) ++ getVariables(q)
      case p ->: q => getVariables(p) ++ getVariables(q)
      case p <-> q => getVariables(p) ++ getVariables(q)
      case ~(p) => getVariables(p)
      case False | True => Set()
      case v: AnyVariable => Set(v)
    }

    def reduce(f: Formula, subst: Map[AnyVariable, Boolean]): Boolean = {
      def reduce(f: Formula): Boolean = f match {
        case p /\ q => reduce(p) && reduce(q)
        case p \/ q => reduce(p) || reduce(q)
        case p ->: q => !reduce(p) || reduce(q)
        case p <-> q => reduce(p) == reduce(q)
        case ~(p) => !reduce(p)
        case False => false
        case True => true
        case v: AnyVariable => subst(v)
      }
      reduce(f)
    }

    val variables = getVariables(f).toSeq

    variables.combinations(variables.size).forall(trues => reduce(f, variables.map(v => v -> trues.contains(v)).toMap))
  }

  implicit class FormulaTester[A <: Formula](f: A) {
    def testTautology(): Theorem[A] = {
      prove(f) match {
        case Some(result) =>
          result =?= f
          result
        case None =>
          fail("Tableaux did not manage to prove fact")
      }
    }
    def testUnprovable(): Unit = {
      val result = prove(f)
      assert(result.isEmpty, "Tableaux solved an unprovable fact (!)")
    }
  }

  test("primitives") {
    def check(f: Formula): Unit = {
      if(isTautology(f)) {
        f.testTautology()
      } else {
        f.testUnprovable()
      }
    }

    for(a <- constant) { // Constants
      check(a)
    }
    for { // Unary
      op <- unary
      a <- constant
    } {
      check(op(a))
    }
    for { // Binary
      op <- binary
      a <- constant
      b <- constant
    } {
      check(op(a, b))
    }
  }

  private val (p, q, r) = (Variable["p"], Variable["q"], Variable["r"])

  test("modus ponens") {
    ((p ->: q) ->: p ->: q).testTautology()
  }

  test("and iff") {
    (((p ->: q ->: False) ->: False) <-> (p /\ q)).testTautology()
  }

  test("or iff") {
    ((~p ->: ~q ->: False) <-> (p \/ q)).testTautology()
  }

  test("or associative") {
    ((p \/ (q \/ r)) <-> ((p \/ q) \/ r)).testTautology()
  }
}
