package lam2gmu_annot

class AST {
  type VarType
  type BindVarType

  sealed abstract class Type
  case class TVar(name: VarType) extends Type {
    override def toString: String = name.toString
  }
  object TUnit extends Type {
    override def toString: String = "1"
  }
  case class Tuple(t1: Type, t2: Type) extends Type {
    override def toString: String = "(" + t1 + " * " + t2 + ")"
  }
  case class Fun(arg: Type, res: Type) extends Type {
    override def toString: String = "(" + arg + " -> " + res + ")"
  }
  case class GADT(args: Seq[Type], name: String) extends Type {
    override def toString: String =
      "(" + args.map(_.toString).mkString(",") + ")" + name
  }
  case class Forall(arg: BindVarType, ttyp: Type) extends Type {
    override def toString: String = "∀" + arg + "." + ttyp
  }

  // we don't do value/expression discrimination at AST class level, but add a method that decides it
  sealed abstract class Expression {
    def isValue: Boolean
  }

  case class LamVar(name: VarType) extends Expression {
    override def isValue: Boolean = true

    override def toString: String = name.toString
  }

  // FixVars are represented by $x in the syntax, TODO remove them
  case class FixVar(name: VarType) extends Expression {
    override def isValue: Boolean = false

    override def toString: String = "$" + name
  }

  case class ConstructorApp(name: String, types: Seq[Type], arg: Expression)
      extends Expression {
    override def isValue: Boolean = arg.isValue
  }

  object VUnit extends Expression {
    override def isValue: Boolean = true
    override def toString: String = "<>"
  }

  case class VTuple(fst: Expression, fstTyp: Type, snd: Expression, sndTyp: Type) extends Expression {
    override def isValue: Boolean = fst.isValue && snd.isValue
    override def toString: String = "<" + fst + ": " + fstTyp + ", " + snd + ": " + sndTyp + ">"
  }

  case class Fst(e: Expression) extends Expression {
    override def isValue: Boolean = false
    override def toString: String = "fst(" + e + ")"
  }

  case class Snd(e: Expression) extends Expression {
    override def isValue: Boolean = false
    override def toString: String = "snd(" + e + ")"
  }

  case class Lambda(arg: BindVarType, argType: Type, body: Expression)
      extends Expression {
    override def isValue: Boolean = true
    override def toString: String = "λ" + arg + ":" + argType + "." + body
  }

  case class Application(fun: Expression, arg: Expression) extends Expression {
    override def isValue: Boolean = false
    override def toString: String = fun + " (" + arg + ")"
  }

  case class TypeLambda(arg: BindVarType, body: Expression) extends Expression {
    if (!body.isValue) {
      throw new RuntimeException("TypeLambda expects a value, got: " + body)
    }
    override def isValue: Boolean = true
    override def toString: String = "Λ" + arg + "." + body
  }

  case class TypeApplication(e: Expression, arg: Type) extends Expression {
    override def isValue: Boolean = false
    override def toString: String = e + "[" + arg + "]"
  }

  case class Fix(selfName: BindVarType, selfType: Type, body: Expression)
      extends Expression {
    if (!body.isValue) {
      throw new RuntimeException("Fix expects a value, got: " + body)
    }
    override def isValue: Boolean = false
    override def toString: String =
      "fix " + selfName + ":" + selfType + "." + body
  }

  case class PatConstructor(name: String, args: Seq[BindVarType], arg: BindVarType)
  type Pattern = PatConstructor

  object Pattern {
    private def isLeaf(pat: Pattern): Boolean = true

    def isNotNested(pat: Pattern): Boolean = true

    def ctor(
        name: String,
        args: Seq[BindVarType],
        varname: BindVarType
    ): PatConstructor =
      PatConstructor(name, args, varname)

    implicit class PatSyntax(pat: Pattern) {
      def `->`(body: Expression): Clause = Clause(pat, body)
    }
  }

  case class Clause(pattern: Pattern, body: Expression) {
    override def toString: String = pattern + " => " + body
  }

  case class CaseOf(e: Expression, gadtName: String, clauses: Seq[Clause], retType: Type) extends Expression {
    override def isValue: Boolean = false
    override def toString: String =
      "match " + e + " as " + gadtName + " returning " + retType + " with " + clauses.map(_.toString).mkString(" | ")
  }

  case class Let(name: BindVarType, bound: Expression, body: Expression)
      extends Expression {
    override def isValue: Boolean = false
    override def toString: String =
      "let " + name + " = " + bound + " in " + body
  }
}

object ASTs {
  object ConcreteSyntax extends AST {
    override type VarType = String
    override type BindVarType = String
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
  }
}
