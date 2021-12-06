package encoding

import lam2gmu_annot.ASTs.{ConcreteSyntax => Lam}
import pdot.ASTs.{ConcreteSyntax => pDOT}
import utils.FreshNameGenerator

class Encoder {
  type TypeSubst = Map[String, pDOT.Typ]
  type FVarSubst = Map[String, pDOT.Term]

  private val nameGen = new FreshNameGenerator

  object Constants {
    val Env = "env"
    val Lib = "lib"
    val Unit = "Unit"
    val UnitCtor = "unit"
    val Tuple = "Tuple"
    val TupleCtor = "tuple"
    val TupleFstTypLabel = "T1"
    val TupleSndTypLabel = "T2"
    val TupleFstElem = "fst"
    val TupleSndElem = "snd"
    val GenericTypName = "GenT"

    def GadtNthTyp(ix: Int): String  = "A" + ix
    def GadtCtorFunction(ctorName: String): String = ctorName.toLowerCase
    def GadtCtorSubtype(name: String, ctorIx: Int): pDOT.Typ = pDOT.PathTyp(pDOT.Path(Env), name) // + "c" + ctorIx)
    def GadtExistentialTypeName(ix: Int): String = "B" + ix

    val UnitTyp = pDOT.PathTyp(pDOT.Path(Lib), Unit)
    val UnitVal = pDOT.PathTrm(pDOT.Path(Lib, Seq(UnitCtor)))
    val TupleTyp = pDOT.PathTyp(pDOT.Path(Lib), Tuple)

    val FixName = "fix"
    val Pmatch = "pmatch"
    val Data = "data"
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
        pDOT.And(pDOT.RecTyp(Constants.TupleFstTypLabel, T1, T1), pDOT.RecTyp(Constants.TupleSndTypLabel, T2, T2))
      )
    }
    case Lam.Fun(argT, retT) =>
      val argName = nameGen.fresh()
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
      val retTp = translateType(ttyp, subst + (arg -> argRef))
      pDOT.AllTyp(argName, argTp, retTp)
  }

  def translateExpr(expr: Lam.Expression): pDOT.Term = translateExpr(expr, Map.empty, Map.empty)
  def translateExpr(expr: Lam.Expression, fixSubst: FVarSubst, typeSubst: TypeSubst): pDOT.Term = expr match {
    case Lam.LamVar(name) => pDOT.PathTrm(pDOT.Path(name))
    case Lam.FixVar(name) => fixSubst(name)

    case Lam.ConstructorApp(name, types, arg) =>
      val ts = nameGen.fresh("ts")
      val v = nameGen.fresh("v")

      val ptypes = types.zipWithIndex.map{case (typ, ix) =>
        (Constants.GadtExistentialTypeName(ix + 1), translateType(typ, typeSubst))
      }
      val tsVal = pDOT.ValTrm(pDOT.ValObject(nameGen.fresh(), recTyp(ptypes), recDef(ptypes)))
      val argExpr = translateExpr(arg, fixSubst, typeSubst)

      pDOT.LetTrm(
        ts, tsVal,
        pDOT.LetTrm(v, argExpr,
          translateApplication(
            pDOT.Path(Constants.Env, Seq(Constants.GadtCtorFunction(name))),
            pDOT.Path(ts),
            pDOT.Path(v)
          )
        )
      )

    case Lam.VUnit => Constants.UnitVal

    case Lam.VTuple(fst, fstTyp, snd, sndTyp) =>
      val v1 = nameGen.fresh("v1")
      val v2 = nameGen.fresh("v2")

      val labels = Seq(
        (Constants.TupleFstTypLabel, translateType(fstTyp, typeSubst)),
        (Constants.TupleSndTypLabel, translateType(sndTyp, typeSubst))
      )
      val tl = nameGen.fresh("tl")
      val typeLabel = pDOT.ValTrm(pDOT.ValObject(nameGen.fresh(), recTyp(labels), recDef(labels)))

      pDOT.LetTrm(
        v1, translateExpr(fst, fixSubst, typeSubst),
        pDOT.LetTrm(
          v2, translateExpr(snd, fixSubst, typeSubst),
          pDOT.LetTrm(
            tl, typeLabel,
            translateApplication(
              pDOT.Path(Constants.Lib, Seq(Constants.TupleCtor)),
              pDOT.Path(tl),
              pDOT.Path(v1),
              pDOT.Path(v2)
            )
          )
        )
      )

    case Lam.Fst(e) =>
      val v = nameGen.fresh("v")
      pDOT.LetTrm(
        v, translateExpr(e, fixSubst, typeSubst),
        pDOT.PathTrm(pDOT.Path(v, Seq(Constants.TupleFstElem)))
      )
    case Lam.Snd(e) =>
      val v = nameGen.fresh("v")
      pDOT.LetTrm(
        v, translateExpr(e, fixSubst, typeSubst),
        pDOT.PathTrm(pDOT.Path(v, Seq(Constants.TupleSndElem)))
      )

    case Lam.Lambda(arg, argType, body) =>
      pDOT.ValTrm(
        pDOT.ValLambda(
          arg,
          translateType(argType, typeSubst),
          translateExpr(body, fixSubst, typeSubst)
        )
      )

    case Lam.Application(fun, arg) =>
      val v1 = nameGen.fresh("v1")
      val v2 = nameGen.fresh("v2")
      pDOT.LetTrm(
        v1, translateExpr(fun, fixSubst, typeSubst),
        pDOT.LetTrm(
          v2, translateExpr(arg, fixSubst, typeSubst),
          pDOT.AppTrm(pDOT.Path(v1), pDOT.Path(v2))
        )
      )

    case Lam.TypeLambda(arg, body) =>
      val A = arg
      pDOT.ValTrm(
        pDOT.ValLambda(
          A, pDOT.RecTyp(Constants.GenericTypName, pDOT.Bot, pDOT.Top),
          translateExpr(body, fixSubst, typeSubst + (arg -> pDOT.PathTyp(pDOT.Path(A), Constants.GenericTypName)))
        )
      )

    case Lam.TypeApplication(e, arg) =>
      val v = nameGen.fresh("v")
      val tl = nameGen.fresh("tl")
      val tlVal = genericTl(translateType(arg, typeSubst))
      pDOT.LetTrm(
        v, translateExpr(e, fixSubst, typeSubst),
        pDOT.LetTrm(
          tl, tlVal,
          pDOT.AppTrm(pDOT.Path(v), pDOT.Path(tl))
        )
      )

    case Lam.Fix(selfName, selfType, body) =>
      val hlpObjName = nameGen.fresh("hlp")
      val selfObjName = nameGen.fresh("self")

      val fixArgName = nameGen.fresh()

      val fixTyp = pDOT.AllTyp(
        fixArgName,
        Constants.UnitTyp,
        translateType(selfType, typeSubst)
      )

      val selfRef = pDOT.AppTrm(
        pDOT.Path(selfObjName, Seq(Constants.FixName)),
        pDOT.Path(Constants.Lib, Seq(Constants.UnitCtor))
      )

      val hlpObjVal = pDOT.ValTrm(
        pDOT.ValObject(
          selfName,
          pDOT.RecTrm(Constants.FixName, fixTyp),
          Seq(
            pDOT.DefTrmVal(
              Constants.FixName,
              pDOT.ValLambda(
                fixArgName,
                Constants.UnitTyp,
                translateExpr(body, fixSubst + (selfName -> selfRef), typeSubst)
              )
            )
          )
        )
      )

      pDOT.LetTrm(
        hlpObjName, hlpObjVal,
        pDOT.AppTrm(
          pDOT.Path(hlpObjName, Seq(Constants.FixName)),
          pDOT.Path(Constants.Lib, Seq(Constants.UnitCtor))
        )
      )

    case Lam.Let(name, bound, body) =>
      pDOT.LetTrm(
        name,
        translateExpr(bound, fixSubst, typeSubst),
        translateExpr(body, fixSubst, typeSubst)
      )

    case Lam.CaseOf(e, name, clauses, retType) =>
      val tl = nameGen.fresh("tl")
      val v = nameGen.fresh("v")
      val caseNames = clauses.map(_ => nameGen.fresh("case"))

      val tlVal = genericTl(translateType(retType, typeSubst))
      val cases = clauses.zipWithIndex.map { case (Lam.Clause(Lam.PatConstructor(name, typArgs, dataArg), body), ix) =>
        val clauseArgName = nameGen.fresh("arg")
        val argType = pDOT.And(Constants.GadtCtorSubtype(name, ix), pDOT.SingletonTyp(pDOT.Path(v)))
        val newTypSubst = typArgs.zipWithIndex.foldLeft(typeSubst) { case (subst, (argName, ix)) =>
          subst + (argName -> pDOT.PathTyp(pDOT.Path(clauseArgName), Constants.GadtExistentialTypeName(ix + 1)))
        }

        val resName = nameGen.fresh("res")

        val pBody =
          pDOT.LetTrm(
            dataArg, pDOT.PathTrm(pDOT.Path(clauseArgName, Seq(Constants.Data))),
            pDOT.LetTrm(
              resName, translateExpr(body, fixSubst, newTypSubst),
              pDOT.PathTrm(pDOT.Path(resName))
            )
          )
        pDOT.ValTrm(
          pDOT.ValLambda(
            clauseArgName, argType, pBody
          )
        )
      }

      pDOT.LetTrm(
        tl, tlVal,
        pDOT.LetTrm(
          v, translateExpr(e, fixSubst, typeSubst),
          manyDeclarations(
            caseNames,
            cases,
            translateApplication(Seq(pDOT.Path(v, Seq(Constants.Pmatch)), pDOT.Path(tl)) ++ caseNames.map(pDOT.Path(_)):_*)
          )
        )
      )
  }

  def recTyp1(description: (String, pDOT.Typ)): pDOT.Typ =
    pDOT.RecTyp(description._1, description._2, description._2)

  def intersectTypes(types: Seq[pDOT.Typ]): pDOT.Typ = types match {
    case Seq() => pDOT.Top
    case Seq(first, rest @ _*) =>
      rest.foldLeft(first)(pDOT.And)
  }

  def recTyp(types: Seq[(String, pDOT.Typ)]): pDOT.Typ = intersectTypes(types.map(recTyp1))

  def recDef(types: Seq[(String, pDOT.Typ)]): Seq[pDOT.Definiton] =
    types.map(pDOT.DefTyp.tupled)

  def genericTl(typ: pDOT.Typ): pDOT.Term = pDOT.ValTrm(
    pDOT.ValObject(
      nameGen.fresh(),
      pDOT.RecTyp(Constants.GenericTypName, typ, typ),
      Seq(pDOT.DefTyp(Constants.GenericTypName, typ))
    )
  )

  def manyDeclarations(names: Seq[String], values: Seq[pDOT.Term], result: pDOT.Term): pDOT.Term =
    names.zip(values).foldRight(result) { case ((name, value), acc) => pDOT.LetTrm(name, value, acc) }

  def translateApplication(paths: pDOT.Path*): pDOT.Term = paths match {
    case Seq(first, second) =>
      pDOT.AppTrm(first, second)
    case Seq(first, second, rest @ _*) =>
      val name = nameGen.fresh("partialApp")
      pDOT.LetTrm(
        name, pDOT.AppTrm(first, second),
        translateApplication((Seq(pDOT.Path(name)) ++ rest): _*)
      )
    case _ =>
      throw new IllegalArgumentException(s"Trying to translate an application of ${paths} -- not enough terms to apply.")
  }
}

