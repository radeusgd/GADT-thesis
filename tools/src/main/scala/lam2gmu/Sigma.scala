package lam2gmu

case class GADTConstructor(name: String) // TODO more info coming soon
case class GADTDef(name: String, ctors: Seq[GADTConstructor])

case class Sigma(gadts: Seq[GADTDef]) {
  def resolveGadt(name: String): GADTDef =
    gadts
      .find(_.ctors.exists(_.name == name))
      .getOrElse(throw new IllegalArgumentException(s"Ctor $name not found"))

  def resolveCtorId(name: String): (String, Int) = {
    val gdef = resolveGadt(name)
    val (_, ind) = gdef.ctors.zipWithIndex
      .find(_._1.name == name)
      .getOrElse(throw new IllegalStateException("Impossible"))
    (gdef.name, ind)
  }
}
