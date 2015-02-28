package org.kframework.tiny

import org.kframework.tiny.matcher.Anywhere

object Substitution {
  implicit def apply(self: K): Substitution = new Substitution(self)
}

class Substitution(self: K) {

  import org.kframework.tiny.Substitution._

  def substitute(substitution: Map[KVar, K]): K = {
    doSubstitution(substitution)
  }

  private def doSubstitution(substitution: Map[KVar, K]) =
    self match {
      case v: KVar => substitution.get(v) map { _.substitute(substitution) } getOrElse v
      case Anywhere(l, p, _) => substitution(l.TOPVariable).substitute(substitution + (l.HOLEVariable -> p))
      case b: Binding => b.klabel(b.variable, b.value.substitute(substitution))
      case KApp(l, ks, att) =>
        l(ks map { x: K => x.substitute(substitution) }, att)
      case e => e
    }
}
