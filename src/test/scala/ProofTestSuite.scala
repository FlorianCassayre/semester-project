import org.scalatest.funsuite.AnyFunSuite
import theory.fol.FOL

abstract class ProofTestSuite extends AnyFunSuite with FOL {

  private val reflectiveInstanciator: Formula => Theorem[Formula] = {
    val clazz = Axiom.getClass
    val methods = clazz.getDeclaredMethods.filter(_.getName == "apply")
    val method = methods.filter(_.getParameterCount == 2).filter(_.getParameterTypes.tail.head.isPrimitive).head
    method.setAccessible(true)

    f => method.invoke(Axiom, f, false).asInstanceOf[Theorem[Formula]]
  }

  implicit def asTheorem[F <: Formula](f: F): Theorem[F] = reflectiveInstanciator(f).asInstanceOf[Theorem[F]]

  implicit class TheoremTester[A <: Formula](thm: Theorem[A]) {
    def =?=(f: A): Unit = {
      assert(thm.isValid, "Theorem is invalid")
      assert(!thm.isDirty, "Theorem contains unproven branches")
      assert(thm.formula === f)
    }
  }
}
