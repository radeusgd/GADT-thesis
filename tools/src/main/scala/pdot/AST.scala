package pdot

class AST {
  type VarType
  type BindVarType
  type TermLabelType
  type TypeLabelType

  case class Path(receiver: VarType, fields: Seq[TermLabelType] = Seq.empty) {
    override def toString: String = receiver.toString + fields.map("." + _).mkString
  }

  sealed trait Typ
  case object Top extends Typ {
    override def toString: String = "⊤"
  }
  case object Bot extends Typ {
    override def toString: String = "⊥"
  }
  case class RecTyp(A: TypeLabelType, lowerBound: Typ, upperBound: Typ) extends Typ {
    override def toString: String = {
      if (lowerBound == upperBound) s"{$A == $lowerBound}"
      else s"{$A: $lowerBound..$upperBound}"
    }
  }
  case class RecTrm(a: TermLabelType, typ: Typ) extends Typ {
    override def toString: String = s"{$a: $typ}"
  }
  case class And(t1: Typ, t2: Typ) extends Typ {
    override def toString: String = s"($t1 ∧ $t2)"
  }
  case class PathTyp(path: Path, label: TypeLabelType) extends Typ {
    override def toString: String = path.toString + "." + label
  }
  case class RecursiveTyp(x: BindVarType, t: Typ) extends Typ {
    override def toString: String = s"μ($x: $t)"
  }
  case class AllTyp(x: BindVarType, arg: Typ, ret: Typ) extends Typ {
    override def toString: String = s"∀($x: $arg) $ret"
  }
  case class SingletonTyp(path: Path) extends Typ {
    override def toString: String = s"$path.type"
  }

  sealed trait Term
  case class ValTrm(v: Value) extends Term {
    override def toString: String = v.toString
  }
  case class AppTrm(p1: Path, p2: Path) extends Term {
    override def toString: String = s"$p1 $p2"
  }
  case class LetTrm(name: BindVarType, t1: Term, t2: Term) extends Term {
    override def toString: String = s"let $name = ($t1) in $t2"
  }
  case class PathTrm(p: Path) extends Term {
    override def toString: String = p.toString
  }

  sealed trait Value
  case class ValObject(x: BindVarType, typ: Typ, defs: Seq[Definiton]) extends Value {
    override def toString: String = s"ν($x: $typ){ ${defs.mkString(";")} }"
  }
  case class ValLambda(x: BindVarType, typ: Typ, body: Term) extends Value {
    override def toString: String = s"λ($x: $typ) $body"
  }

  sealed trait Definiton
  case class DefTyp(A: TypeLabelType, typ: Typ) extends Definiton {
    override def toString: String = s"$A =v $typ"
  }
  case class DefTrmVal(a: TermLabelType, v: Value) extends Definiton {
    override def toString: String = s"$a =v $v"
  }
  case class DefTrmPath(a: TermLabelType, p: Path) extends Definiton {
    override def toString: String = s"$a =p $p"
  }
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
