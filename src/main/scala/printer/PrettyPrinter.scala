package printer

import theory.fol.FOL._
import theory.NBGTheory._

object PrettyPrinter extends App {

  def prettify(f: Formula, minimal: Boolean = true, spaces: Boolean = false): String = {
    def prettify(f: Formula): String = {

      def isAtomic(formula: Formula): Boolean = formula match {
        case _ === _ | ~(_) | Variable(_) | False | True => true
        case _ => false
      }

      def prettifyParen(f: Formula): String = if(isAtomic(f)) prettify(f) else s"(${prettify(f)})"

      def binOp(op: String, a: Formula, b: Formula): String = {
        def precedence(f: Formula): Int = f match {
          case _ if isAtomic(f) => 5
          case _ /\ _ => 4
          case _ \/ _ => 3
          case _ ->: _ => 2
          case _ <-> _ => 1
        }

        val (pf, pa, pb) = (precedence(f), precedence(a), precedence(b))
        val l = if(pf >= pa) prettifyParen(a) else prettify(a)
        val r = if(pb < pf) prettifyParen(b) else prettify(b)
        s"$l$op$r"
      }

      f match {
        case Variable(id) => id
        case False => "⊥"
        case True => "⊤"
        case ~(p) => s"¬${prettifyParen(p)}"
        case p /\ q => binOp("∧", p, q)
        case p \/ q => binOp("∨", p, q)
        case p ->: q => binOp("→", p, q)
        case p <-> q => binOp("↔", p, q)
        case x === y => s"(${prettifySet(x)}=${prettifySet(y)})"
      }
    }

    prettify(f)
  }

  def prettifySet(s: AnySet): String = s match {
    case _ => s.toString
  }

}
