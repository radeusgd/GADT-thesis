package lam2gmu_annot

import ASTs.ConcreteSyntax._
import scala.util.matching.Regex
import scala.util.parsing.combinator._
import scala.util.parsing.input.{NoPosition, Position, Positional, Reader}

sealed trait Token extends Positional {
  def str: String
}
case class Identifier(override val str: String) extends Token
case class FixIdentifier(override val str: String) extends Token
case class Special(override val str: String) extends Token

object Lexer extends RegexParsers {
  override def skipWhitespace = true
  override val whiteSpace: Regex = "[ \t\r\f\n]+".r

  def fixidentifier: Parser[FixIdentifier] = {
    """\$[a-zA-Z][a-zA-Z0-9_]*""".r ^^ { str => FixIdentifier(str.drop(1)) }
  }

  def identifier: Parser[Identifier] = {
    "[a-zA-Z][a-zA-Z0-9_]*".r ^^ Identifier
  }

  def special: Parser[Special] = {
    """<>|->|=>|[=.<>\(\)\[\]{}\*\|,;:∀1λΛ]""".r ^^ Special
  }

  def token: Parser[Token] = special | fixidentifier | identifier

  def tokens: Parser[List[Token]] = phrase(rep1(token))

  def apply(code: String): Either[String, List[Token]] = {
    parse(tokens, code) match {
      case NoSuccess(msg, next)  => Left("TokenizerError: "+ msg + "; before: " + next.source)
      case Success(result, next) => Right(result)
    }
  }
}

object LamParser extends PackratParsers {
  override type Elem = Token
  class TokenReader(tokens: Seq[Token]) extends Reader[Token] {
    override def source: CharSequence = tokens.mkString(";")
    override def first: Token = tokens.head
    override def atEnd: Boolean = tokens.isEmpty
    override def pos: Position =
      tokens.headOption.map(_.pos).getOrElse(NoPosition)
    override def rest: Reader[Token] = new TokenReader(tokens.tail)
  }

  //<editor-fold desc="Syntax helpers">
  def identifier: Parser[String] =
    elem("Identifier", _.isInstanceOf[Identifier]) ^^ (_.str)
  def fixidentifier: Parser[String] =
    elem("FixIdentifier", _.isInstanceOf[FixIdentifier]) ^^ (_.str)
  def keyword(keyword: String): Parser[Unit] = elem(Identifier(keyword)) ^^^ ()
  def $(special: String): Parser[Unit] =
    elem(
      "FixIdentifier",
      e => e.isInstanceOf[Special] && e.str == special
    ) ^^^ ()
  def braces[A](p: => Parser[A]): Parser[A] = $("(") ~> p <~ $(")")
  def brackets[A](p: => Parser[A]): Parser[A] = $("[") ~> p <~ $("]")
  //</editor-fold>

  // types
  def ttype: Parser[Type] = ttuple | tfun | ttype2

  def tunit: Parser[Type] = $("1") ^^^ TUnit
  def tvar: Parser[Type] = identifier ^^ TVar
  def ttype2: Parser[Type] = tunit | tforall | tgadt | tvar | braces(ttype)
  def ttuple: Parser[Type] =
    (ttype2 ~ $("*") ~ ttype) ^^ { case t1 ~ _ ~ t2 => Tuple(t1, t2) }
  def tfun: Parser[Type] =
    (ttype2 ~ $("->") ~ ttype) ^^ { case t1 ~ _ ~ t2 => Fun(t1, t2) }
  def tforall: Parser[Type] =
    (($("∀") | keyword("forall")) ~ identifier ~ $(".") ~ ttype2) ^^ {
      case _ ~ i ~ _ ~ t2 => Forall(i, t2)
    }
  def tgadt: Parser[Type] =
    braces(repsep(ttype, $(","))) ~ identifier ^^ {
      case args ~ i => GADT(args, i)
    }

  def parseType(code: String): Either[String, Type] = {
    Lexer(code).flatMap(tokens =>
      phrase(ttype)(new TokenReader(tokens)) match {
        case NoSuccess(msg, next)  => Left(msg)
        case Success(result, next) => Right(result)
      }
    )
  }

  // expressions
  def expr: Parser[Expression] = application | typeapplication | expr2
  def expr2: Parser[Expression] =
    let | unit | tuple | fst | snd | lambda | typelambda | constructor | fix | caseOf | lamvar | fixvar | fix | braces(
      expr
    )
  def lamvar: Parser[LamVar] = identifier ^^ LamVar
  def fixvar: Parser[FixVar] = fixidentifier ^^ FixVar
  def constructor: Parser[ConstructorApp] =
    identifier ~ brackets(repsep(ttype, $(","))) ~ braces(expr) ^^ {
      case id ~ types ~ ex => ConstructorApp(id, types, ex)
    }
  def unit: Parser[Expression] = $("<>") ^^^ VUnit
  def tuple: Parser[VTuple] =
    $("<") ~ expr ~ $(":") ~ ttype ~ $(",") ~ expr ~ $(":") ~ ttype ~ $(">") ^^ {
      case _ ~ e1 ~ _ ~ t1 ~ _ ~ e2 ~ _ ~ t2 ~ _ => VTuple(e1, t1, e2, t2)
    }
  def fst: Parser[Fst] = keyword("fst") ~> braces(expr) ^^ Fst
  def snd: Parser[Snd] = keyword("snd") ~> braces(expr) ^^ Snd
  def lambda: Parser[Lambda] =
    ($("λ") | keyword("lam")) ~ identifier ~ $(":") ~ ttype ~ $(".") ~ expr ^^ {
      case _ ~ arg ~ _ ~ typ ~ _ ~ ex => Lambda(arg, typ, ex)
    }
  def application: Parser[Application] =
    expr2 ~ braces(expr) ^^ { case e1 ~ e2 => Application(e1, e2) }
  def typelambda: Parser[TypeLambda] =
    ($("Λ") | keyword("Lam")) ~ identifier ~ $(".") ~ expr ^^ {
      case _ ~ alpha ~ _ ~ v => TypeLambda(alpha, v)
    }
  def typeapplication: Parser[TypeApplication] =
    expr2 ~ brackets(ttype) ^^ { case e ~ t => TypeApplication(e, t) }
  def fix: Parser[Fix] =
    keyword("fix") ~ fixidentifier ~ $(":") ~ ttype ~ $(".") ~ expr ^^ {
      case _ ~ f ~ _ ~ t ~ _ ~ v => Fix(f, t, v)
    }
  def caseOf: Parser[CaseOf] =
    keyword("matchgadt") ~ expr ~ keyword("as") ~ identifier ~ keyword("returning") ~ ttype ~ keyword("with") ~ $("{") ~ rep1sep(
      clause,
      $("|")
    ) ~ $("}") ^^ { case _ ~ e ~ _ ~ name ~ _ ~ typ ~ _ ~  _ ~ cls ~ _ => CaseOf(e, name, cls, typ) }
  def let: Parser[Let] =
    keyword("let") ~ identifier ~ $("=") ~ expr ~ keyword("in") ~ expr ~ keyword("end") ^^ {
      case _ ~ x ~ _ ~ e1 ~ _ ~ e2 ~ _ => Let(x, e1, e2)
    }

  def clause: Parser[Clause] =
    pattern ~ $("=>") ~ expr ^^ { case p ~ _ ~ e => Clause(p, e) }

  def pattern: Parser[Pattern] = patCons
  def patCons: Parser[Pattern] =
    identifier ~ brackets(repsep(identifier, $(","))) ~ braces(identifier) ^^ {
      case c ~ a ~ p => PatConstructor(c, a, p)
    }

  def parseExpr(code: String): Either[String, Expression] = {
    Lexer(code).flatMap(tokens =>
      phrase(expr)(new TokenReader(tokens)) match {
        case NoSuccess(msg, next) =>
          Left("ParserError: "+ msg + "; before: " + next.first)
        case Success(result, next) => Right(result)
      }
    )
  }
}
