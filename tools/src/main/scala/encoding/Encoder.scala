package encoding

import lam2gmu.ASTs.{ConcreteSyntax => Lam}
import pdot.ASTs.{ConcreteSyntax => pDOT}
import utils.FreshNameGenerator

class Encoder {
  type TypeSubst = Map[String, pDOT.Typ]

  private val freshNameGenerator = new FreshNameGenerator

  object Constants {
    val Env = "env"
    val Lib = "lib"
    val Unit = "Unit"
    val Tuple = "Tuple"
    val TupleFstTyp = "T1"
    val TupleSndTyp = "T2"
    val GenericTypName = "GenT"

    def GadtNthTyp(ix: Int): String  = "T" + ix

    val UnitTyp = pDOT.PathTyp(pDOT.Path(Lib), Unit)
    val TupleTyp = pDOT.PathTyp(pDOT.Path(Lib), Tuple)
  }

//  def translateType(typ: Lam.Type): pDOT.Typ = translateType(typ, Map.empty)
  def translateType(typ: Lam.Type, subst: TypeSubst):pDOT.Typ = typ match {
    case Lam.TVar(name) => subst(name)
    case Lam.TUnit => Constants.UnitTyp
    case Lam.Tuple(t1, t2) => {
      val T1 = translateType(t1, subst)
      val T2 = translateType(t2, subst)
      pDOT.And(
        Constants.TupleTyp,
        pDOT.And(pDOT.RecTyp("T1", T1, T1), pDOT.RecTyp("T2", T2, T2))
      )
    }
    case Lam.Fun(argT, retT) =>
      val argName = freshNameGenerator.generateFreshName()
      val argTp = translateType(argT, subst)
      val retTp = translateType(retT, subst)
      pDOT.AllTyp(argName, argTp, retTp)
    case Lam.GADT(args, name) =>
      args.zipWithIndex.foldLeft[pDOT.Typ](pDOT.PathTyp(pDOT.Path(Constants.Env), name)) { case (acc, (argT, ix)) =>
        val label = Constants.GadtNthTyp(ix + 1)
        val argTp = translateType(argT, subst)
        pDOT.And(acc, pDOT.RecTyp(label, argTp, argTp))
      }
    case Lam.Forall(arg, ttyp) =>
      val argName = arg // freshNameGenerator.generateFreshName()
      val argTp = pDOT.RecTyp(Constants.GenericTypName, pDOT.Bot, pDOT.Top)
      val argRef = pDOT.PathTyp(pDOT.Path(argName), Constants.GenericTypName)
      val retTp = translateType(ttyp, subst.updated(arg, argRef))
      pDOT.AllTyp(argName, argTp, retTp)
  }
}
