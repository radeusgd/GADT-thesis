package lam2gu.testing

import lam2gu.ASTs.ConcreteSyntax.{ConstructorApp, Expression, VUnit}
import lam2gu.{
  CoqBackend,
  DeBruijnEncoder,
  GADTConstructor,
  GADTDef,
  LamParser,
  Sigma
}

object NatExample {
  def succ(x: Expression): Expression = ConstructorApp("succ", Seq(), x)
  def zero: Expression = ConstructorApp("zero", Seq(), VUnit)

  val plusCode: String =
    "fix $self:(()Nat -> ()Nat -> ()Nat). λa:()Nat. λb:()Nat." +
      "case a of { " +
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
    val expr = plus.right.get
    val debruijn = DeBruijnEncoder.encode(expr)
    println(debruijn)
    val coq = CoqBackend(sigma).renderExpr(debruijn)
    println(coq)
  }

//  def plusHelper(self: FixVar, a: LamVar, b: LamVar): Expression =
//    CaseOf(
//      a,
//      Seq(
//        Pattern.ctor("zero", Seq(), "_") -> b,
//        Pattern.ctor("succ", Seq(), "n") -> applyFun(self, LamVar("n"), )
//      )
//    )

}
