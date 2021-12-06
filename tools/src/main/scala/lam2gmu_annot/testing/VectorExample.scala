package lam2gmu_annot.testing

import encoding.Encoder
import lam2gmu_annot.ASTs.ConcreteSyntax.Expression
import lam2gmu_annot.{GADTConstructor, GADTDef, LamParser, Sigma}

object VectorExample {
  val zipCode: String =
    """fix $self: (∀a. ∀b. ∀n. ((a,n) Vector -> (b,n) Vector -> (a * b,n) Vector)).
     Λa. Λb. Λn. λva: ((a,n) Vector). λvb: ((b,n) Vector).
     matchgadt va as Vector returning (a * b,n) Vector with {
        Nil[a2](unused) => Nil[a * b](<>)
      | Cons[a2, n2](da) =>
        matchgadt vb as Vector returning (a * b,n) Vector with {
          Nil[b2](unused) => <>
        | Cons[b2, n3](db) =>
            let h = <fst(da) : a2, fst(db) : b2> in
              let t = (((($self[a])[b])[n2]) (snd(da))) (snd(db)) in
                Cons[(a*b),n2](<h : a*b, t : (a*b, n2) Vector>)
              end
            end
        }
     }
  """

  val headCode: String =
    """Λa. Λn. λv: ((a,(n) Succ) Vector).
        matchgadt v as Vector returning a with {
          Nil[a2](unused) => <>
        | Cons[a2, n2](da) => fst(da)
        }
  """

  lazy val headAST = LamParser.parseExpr(headCode)
  lazy val zipAST = LamParser.parseExpr(zipCode)

  val sigma = Sigma(Seq(
    GADTDef("Zero", Seq(GADTConstructor("zero"))),
    GADTDef("Succ", Seq(GADTConstructor("succ"))),
    GADTDef("Vector", Seq(
      GADTConstructor("Nil"),
      GADTConstructor("Cons")
    ))
  ))

  def printStages(name: String, ast: Either[String, Expression]): Unit = {
    println(s"$name:")
    println("Parsed AST:")
    println(ast)
    val expr = ast match {
      case Left(error) =>
        throw new RuntimeException(error)
      case Right(value) => value
    }
    val encoder = new Encoder
    val pdot = encoder.translateExpr(expr)
    println("pDOT:")
    println(pdot)
  }

  def main(args: Array[String]): Unit = {
    printStages("head", headAST)
    printStages("zip", zipAST)
  }

}
