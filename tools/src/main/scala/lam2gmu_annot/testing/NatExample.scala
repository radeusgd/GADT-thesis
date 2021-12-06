package lam2gmu_annot.testing

import encoding.Encoder
import lam2gmu_annot.ASTs.ConcreteSyntax.{ConstructorApp, Expression, VUnit}
import lam2gmu_annot.{GADTConstructor, GADTDef, LamParser, Sigma}

object NatExample {
  def succ(x: Expression): Expression = ConstructorApp("succ", Seq(), x)
  def zero: Expression = ConstructorApp("zero", Seq(), VUnit)

  val plusCode: String =
    "fix $self:(()Nat -> ()Nat -> ()Nat). λa:()Nat. λb:()Nat." +
      "matchgadt a as Nat returning (()Nat) with { " +
      "zero[](unused) => b " +
      "| succ[](n) => ($self(n))(succ[](b)) " +
      "}"

  val plus = LamParser.parseExpr(plusCode)

  val NatDef = {
    val zero = GADTConstructor("zero")
    val succ = GADTConstructor("succ")
    GADTDef("Nat", Seq(zero, succ))
  }
  val sigma = Sigma(Seq(NatDef))

  def main(args: Array[String]): Unit = {
    println(plus)
    val expr = plus match {
      case Left(error) =>
        throw new RuntimeException(s"Parse error: $error")
      case Right(res) => res
    }
    val encoder = new Encoder
    val pdot = encoder.translateExpr(expr)
    println(pdot)
  }
}
