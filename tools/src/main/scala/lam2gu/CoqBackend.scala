package lam2gu

case class CoqBackend(sigma: Sigma) {
  import ASTs.DeBruijnSyntax._
  def renderExpr(expression: Expression): String =
    expression match {
      case LamVar(ref) => s"#${ref.index}"
      case FixVar(ref) => s"#${ref.index}"
      case ConstructorApp(name, types, arg) =>
        val targs = types.map(renderTyp).mkString("[", "; ", "]*")
        val darg = renderExpr(arg)
        val (gadtName, ctorInd) = sigma.resolveCtorId(name)
        s"trm_constructor $targs ($gadtName, $ctorInd) ($darg)"
      case VUnit => "trm_unit"
      case VTuple(fst, snd) =>
        s"trm_tuple (${renderExpr(fst)}) (${renderExpr(snd)})"
      case Fst(e) =>
        s"trm_fst (${renderExpr(e)})"
      case Snd(e) =>
        s"trm_snd (${renderExpr(e)})"
      case Lambda(Binder, argType, body) =>
        s"trm_abs (${renderTyp(argType)}) (${renderExpr(body)})"
      case Application(fun, arg) =>
        s"trm_app (${renderExpr(fun)}) (${renderExpr(arg)})"
      case TypeLambda(Binder, body) =>
        s"trm_tabs (${renderExpr(body)})"
      case TypeApplication(e, arg) =>
        s"trm_tapp (${renderExpr(e)}) (${renderTyp(arg)})"
      case Fix(Binder, selfType, body) =>
        s"trm_fix (${renderTyp(selfType)}) (${renderExpr(body)})"
      case CaseOf(e, clauses) =>
        val (gadtName, cls) = renderClauses(clauses)
        val clsR = cls.mkString("[", "; ", "]*")
        s"trm_matchgadt (${renderExpr(e)}) $gadtName $clsR"
      case Let(Binder, bound, body) =>
        s"trm_app (${renderExpr(bound)}) (${renderExpr(body)})"
    }

  def renderTyp(typ: Type): String =
    typ match {
      case TVar(ref)    => s"##${ref.index}"
      case TUnit         => "typ_unit"
      case Tuple(t1, t2) => s"(${renderTyp(t1)}) ** (${renderTyp(t2)})"
      case Fun(arg, res) => s"(${renderTyp(arg)}) ==> (${renderTyp(res)})"
      case GADT(args, name) =>
        val argsR = args.map(renderTyp).mkString("[", "; ", "]*")
        s"typ_gadt $argsR $name"
      case Forall(Binder, ttyp) =>
        s"typ_all (${renderTyp(ttyp)})"
    }

  def renderClauses(clauses: Seq[Clause]): (String, Seq[String]) = {
    if (clauses.isEmpty) throw new IllegalArgumentException("Empty match")
    case class PatData(name: String, arity: Int, gadt: GADTDef)
    def unwrapPat(clause: Clause): PatData =
      clause.pattern match {
        case PatConstructor(name, args, PatVar(Binder)) =>
          PatData(name, args.length, sigma.resolveGadt(name))
        case _ =>
          throw new IllegalArgumentException(
            "Unsupported match - non GADT or nesting"
          )
      }

    val pats = clauses.map(unwrapPat)
    val mainGadtDef = pats.head.gadt
    val mainGadtName = mainGadtDef.name
    if (!pats.forall(_.gadt.name == mainGadtName)) {
      throw new IllegalArgumentException("Unsupported match - heterogenity")
    }

    val ctorNames = pats.map(_.name)
    if (ctorNames.length != mainGadtDef.ctors.length) {
      throw new IllegalArgumentException(
        "Unsupported match - exhaustivity and distinctness"
      )
    }

    val order =
      ctorNames.zip(mainGadtDef.ctors.map(_.name)).forall(d => d._1 == d._2)
    if (!order) {
      // TODO automatic reordering
      throw new IllegalArgumentException(
        "Unsupported match [WIP] - reorder needed"
      )
    }

    val patsWithBodies = pats.zip(clauses.map(_.body))
    val renderedClauses = patsWithBodies.map {
      case (data, expression) =>
        val clArity = data.arity
        s"clause $clArity (${renderExpr(expression)})"
    }
    (mainGadtName, renderedClauses)
  }
}
