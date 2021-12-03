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

object VectorExample {
  val zipCode: String =
  """fix $self: (∀a. ∀b. ∀n. ((a,n) Vector -> (b,n) Vector -> (a * b,n) Vector)).
     Λa. Λb. Λn. λva: ((a,n) Vector). λvb: ((b,n) Vector). case va of {
        Nil[a2](unused) => Nil[a * b](<>)
      | Cons[a2, n2](da) =>
       case vb of {
         Nil[b2](unused) => <>
       | Cons[b2, n3](db) =>
           let h = <fst(da), fst(db)> in
             let t = (((($self[a])[b])[n2]) (snd(da))) (snd(db)) in
               Cons[(a*b),n2](<h, t>)
             end
           end
       }
     }

  """
  /*

$self[a][b][n2] (snd(da)) (snd(db))
         case vb of {
              Nil[b2](unused) => <>
 Cons[b2, n3](vbdata) =>
                Cons[a2 * b2, n2](<>)
            }

<<fst(vadata), fst(vbdata)>, ((($self[a][b][n]) (snd(vadata))) (snd(vbdata))>
   */

  val zipAST = LamParser.parseExpr(zipCode)

  val sigma = Sigma(Seq(
    GADTDef("Zero", Seq(GADTConstructor("zero"))),
    GADTDef("Succ", Seq(GADTConstructor("succ"))),
    GADTDef("Vector", Seq(
      GADTConstructor("Nil"),
      GADTConstructor("Cons")
    ))
  ))

  def main(args: Array[String]): Unit = {
    println(zipAST)
    val expr = zipAST.right.get
    val debruijn = DeBruijnEncoder.encode(expr)
    println(debruijn)
    val coq = CoqBackend(sigma).renderExpr(debruijn)
    println(coq)
  }

}
