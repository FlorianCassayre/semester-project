package printer

import theory.fol.FOL._
import theory.NBGTheory._

object PrettyPrinter {

  case class Options(spaces: Boolean = false)

  def prettifyFormula(f: Formula)(implicit options: Options = Options()): String = {
    def isAtomic(formula: Formula): Boolean = formula match {
      case _ /\ _ | _ \/ _ | _ ->: _ | _ <-> _ => false
      case _ => true
    }

    def prettifyParenFormula(f: Formula)(implicit options: Options): String = if(isAtomic(f)) prettifyFormula(f) else prettifyParen(prettifyFormula(f))

    def prettifyFormulaOp(op: String, a: Formula, b: Formula)(implicit options: Options): String = {
      def precedence(f: Formula): Int = f match {
        case _ if isAtomic(f) => 5
        case _ /\ _ => 4
        case _ \/ _ => 3
        case _ ->: _ => 2
        case _ <-> _ => 1
      }

      val (pf, pa, pb) = (precedence(f), precedence(a), precedence(b))
      val l = if(pf >= pa) prettifyParenFormula(a) else prettifyFormula(a)
      val r = if(pb < pf) prettifyParenFormula(b) else prettifyFormula(b)
      prettifyInfix(op, l, r)
    }

    f match {
      case Variable(id) => id
      case False => "⊥"
      case True => "⊤"
      case p /\ q => prettifyFormulaOp("∧", p, q)
      case p \/ q => prettifyFormulaOp("∨", p, q)
      case p ->: q => prettifyFormulaOp("→", p, q)
      case p <-> q => prettifyFormulaOp("↔", p, q)
      case Member(x, y) => prettifySetOp("∈", x, y)
      case ~(Member(x, y)) => prettifySetOp("∉", x, y)
      case x === y => prettifySetOp("=", x, y)
      case ~(x === y) => prettifySetOp("≠", x, y)
      case SubsetEqual(x, y) => prettifySetOp("⊆", x, y)
      case ~(SubsetEqual(x, y)) => prettifySetOp("⊈", x, y)
      case SubsetStrict(x, y) => prettifySetOp("⊂", x, y)
      case ~(SubsetStrict(x, y)) => prettifySetOp("⊄", x, y)
      case IsSet(x) => prettifySetFun("M", x)
      case Relation(x) => prettifySetFun("Rel", x)
      case Fnc(x) => prettifySetFun("Fnc", x)
      case ~(p) => s"¬${prettifyParenFormula(p)}"

      case _ => f.toString
    }
  }

  def prettifySet(s: AnySet)(implicit options: Options = Options()): String = {
    def isAtomic(s: AnySet): Boolean = s match {
      case Intersect(_, _) | Union(_, _) | Difference(_, _) | Product(_, _) => false
      case _ => true
    }

    def prettifyParenSet(s: AnySet)(implicit options: Options): String = if(isAtomic(s)) prettifySet(s) else prettifyParen(prettifySet(s))

    def prettifySetOpParen(op: String, x: AnySet, y: AnySet)(implicit options: Options): String = prettifyInfix(op, prettifyParenSet(x), prettifyParenSet(y))

    s match {
      case SetVariable(id) => id
      case EmptySet => "Ø"
      case Universe => "U"
      case SingletonSet(x) => s"{${prettifySet(x)}}"
      case PairSet(x, y) => s"{${prettifySet(x)}${prettifySeparator}${prettifySet(y)}}"
      case OrderedPair(x, y) => s"<${prettifySet(x)}${prettifySeparator}${prettifySet(y)}>"
      case MemberRelation => "∈ᵣ"
      case Complement(x) => s"-${prettifyParenSet(x)}"
      case Intersect(x, y) => prettifySetOpParen("⋂", x, y)
      case Union(x, y) => prettifySetOpParen("⋃", x, y)
      case Difference(x, y) => prettifySetOpParen("∖", x, y)
      case Product(x, y) => prettifySetOpParen("×", x, y)
      case Power(x) => prettifySetFun("P", x)
      case Sum(x) => prettifySetFun("⋃", x)
      case Identity => "I"
      case Infinity => "Inf"
      case Inverse(x) => prettifySetFun("Inv", x)
      case Range(x) => prettifySetFun("R", x)
      case Russell => "Russell"
      case c: SkolemConstant[_] => c.name
      case f: SkolemFunction1[_, _] => prettifySetFun(f.name, f.a)
      case f: SkolemFunction2[_, _, _] => prettifySetFun(f.name, f.a, f.b)
      case f: SkolemFunction3[_, _, _, _] => prettifySetFun(f.name, f.a, f.b, f.c)

      case _ => s.toString
    }
  }

  private def prettifyParen(s: String): String = s"($s)"

  private def prettifyInfix(op: String, l: String, r: String)(implicit options: Options): String =
    if(options.spaces) s"$l $op $r" else s"$l$op$r"

  private def prettifySeparator(implicit options: Options): String = {
    val comma = ","
    if(options.spaces) comma + " " else comma
  }

  private def prettifyPrefix(name: String, args: String*)(implicit options: Options): String =
    if(args.isEmpty) name else s"$name${prettifyParen(args.mkString(prettifySeparator))}"

  private def prettifySetOp(op: String, x: AnySet, y: AnySet)(implicit options: Options): String = prettifyInfix(op, prettifySet(x), prettifySet(y))

  private def prettifySetFun(name: String, args: AnySet*)(implicit options: Options): String = prettifyPrefix(name, args.map(prettifySet): _*)

}
