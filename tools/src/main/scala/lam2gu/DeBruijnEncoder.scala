package lam2gu

import lam2gu.ASTs.{ConcreteSyntax => CS, DeBruijnSyntax => DS}

object DeBruijnEncoder {
  def encode(expression: CS.Expression): DS.Expression =
    encSub(expression, Map.empty, Map.empty)

  case class UnknownIdentifier(name: String)
      extends IllegalArgumentException(s"Unknown identifier $name")

  type Subst = Map[String, Int]

  // TODO rewrite this to use some kind of reader/state monad
  def encSub(
      expresssion: CS.Expression,
      exprSubst: Subst,
      typSubst: Subst
  ): DS.Expression =
    expresssion match {
      case CS.LamVar(name) => DS.LamVar(exprSubst.deref(name))
      case CS.FixVar(name) => DS.FixVar(exprSubst.deref(name))
      case CS.ConstructorApp(name, types, arg) =>
        DS.ConstructorApp(
          name,
          types.map(encSubT(_, typSubst)),
          encSub(arg, exprSubst, typSubst)
        )
      case CS.VUnit => DS.VUnit
      case CS.VTuple(fst, snd) =>
        DS.VTuple(
          encSub(fst, exprSubst, typSubst),
          encSub(snd, exprSubst, typSubst)
        )
      case CS.Fst(e) =>
        DS.Fst(encSub(e, exprSubst, typSubst))
      case CS.Snd(e) =>
        DS.Snd(encSub(e, exprSubst, typSubst))
      case CS.Lambda(arg, argType, body) =>
        DS.Lambda(
          (),
          encSubT(argType, typSubst),
          encSub(body, exprSubst.enterBinder(arg), typSubst)
        )
      case CS.Application(fun, arg) =>
        DS.Application(
          encSub(fun, exprSubst, typSubst),
          encSub(arg, exprSubst, typSubst)
        )
      case CS.TypeLambda(arg, body) =>
        DS.TypeLambda((), encSub(body, exprSubst, typSubst.enterBinder(arg)))
      case CS.TypeApplication(e, arg) =>
        DS.TypeApplication(
          encSub(e, exprSubst, typSubst),
          encSubT(arg, typSubst)
        )
      case CS.Fix(selfName, selfType, body) =>
        DS.Fix(
          (),
          encSubT(selfType, typSubst),
          encSub(body, exprSubst.enterBinder(selfName), typSubst)
        )
      case CS.CaseOf(e, clauses) =>
        DS.CaseOf(
          encSub(e, exprSubst, typSubst),
          clauses.map {
            case CS.Clause(pattern, body) =>
              val (pat, eP, tP) = encPat(pattern, exprSubst, typSubst)
              val encBody = encSub(body, eP, tP)
              DS.Clause(pat, encBody)
          }
        )
      case CS.Let(name, bound, body) =>
        DS.Let(
          (),
          encSub(bound, exprSubst, typSubst),
          encSub(body, exprSubst.enterBinder(name), typSubst)
        )
    }

  def encPat(
      pattern: CS.Pattern,
      exprSubst: Subst,
      typSubst: Subst
  ): (DS.Pattern, Subst, Subst) =
    pattern match {
      case CS.PatVar(name) =>
        (DS.PatVar(()), exprSubst.enterBinder(name), typSubst)
      case CS.PatUnit => (DS.PatUnit, exprSubst, typSubst)
      case CS.PatTuple(fst, snd) =>
        val (fstP, eP, tP) = encPat(fst, exprSubst, typSubst)
        val (sndP, eS, tS) = encPat(snd, eP, tP)
        (DS.PatTuple(fstP, sndP), eS, tS)
      case CS.PatConstructor(name, args, body) =>
        // TODO verify if order is correct here or should be reversed
        val tP = args.foldLeft(typSubst) {
          case (subst, arg) => subst.enterBinder(arg)
        }
        val (bodyPat, eS, tS) = encPat(body, exprSubst, tP)
        (DS.PatConstructor(name, args.map(_ => ()), bodyPat), eS, tS)
    }

  def encSubT(typ: CS.Type, subst: Subst): DS.Type =
    typ match {
      case CS.TVar(name) => DS.TVar(subst.deref(name))
      case CS.TUnit      => DS.TUnit
      case CS.Tuple(t1, t2) =>
        DS.Tuple(
          encSubT(t1, subst),
          encSubT(t2, subst)
        )
      case CS.Fun(arg, res) =>
        DS.Fun(
          encSubT(arg, subst),
          encSubT(res, subst)
        )
      case CS.GADT(args, name) =>
        DS.GADT(args.map(encSubT(_, subst)), name)
      case CS.Forall(arg, ttyp) =>
        DS.Forall((), encSubT(ttyp, subst.enterBinder(arg)))
    }

  implicit class SubstSyntax(substs: Subst) {
    def lift: Subst =
      substs.mapValues(_ + 1)

    def enterBinder(name: String): Subst =
      lift.updated(name, 0)

    def deref(name: String): Int =
      substs.getOrElse(name, throw UnknownIdentifier(name))
  }
}
