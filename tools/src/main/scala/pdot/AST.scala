package pdot

class AST {
  type VarType
  type BindVarType
  type TermLabelType
  type TypeLabelType

  case class Path(receiver: VarType, fields: Seq[TermLabelType] = Seq.empty)

  sealed trait Typ
  case object Top extends Typ
  case object Bot extends Typ
  case class RecTyp(A: TypeLabelType, lowerBound: Typ, upperBound: Typ) extends Typ
  case class RecTrm(a: TermLabelType, typ: Typ) extends Typ
  case class And(t1: Typ, t2: Typ) extends Typ
  case class PathTyp(path: Path, label: TypeLabelType) extends Typ
  case class RecursiveTyp(x: BindVarType, t: Typ) extends Typ
  case class AllTyp(x: BindVarType, arg: Typ, ret: Typ) extends Typ
  case class SingletonTyp(path: Path) extends Typ

  sealed trait Term
  case class ValTrm(v: Value) extends Term
  case class AppTrm(p1: Path, p2: Path) extends Term
  case class LetTrm(t1: Term, t2: Term) extends Term
  case class PathTrm(p: Path) extends Term

  sealed trait Value
  case class ValObject(typ: Typ, defs: Seq[Definiton]) extends Value
  case class ValLambda(typ: Typ, x: BindVarType, body: Term) extends Value

  sealed trait Definiton
  case class DefTyp(A: TypeLabelType, typ: Typ) extends Definiton
  case class DefTrmVal(a: TermLabelType, v: Value) extends Definiton
  case class DefTrmPath(a: TermLabelType, p: Path) extends Definiton
}

object ASTs {
  object ConcreteSyntax extends AST {
    override type VarType = String
    override type BindVarType = String
    override type TermLabelType = String
    override type TypeLabelType = String
  }

  object DeBruijnSyntax extends AST {
    case object Binder {
      override def toString: String = "#"
    }

    case class Ref(index: Int) {
      override def toString: String = s"#$index"
    }

    override type VarType = Ref
    override type BindVarType = Binder.type

    // TODO we want to use the Ai, Bi functions in Coq
    override type TermLabelType = String
    override type TypeLabelType = String
  }
}
