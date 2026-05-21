import scala.util.parsing.combinator.JavaTokenParsers

object LambdaParser extends JavaTokenParsers:
  // % starts a line comment
  override def skipWhitespace = true
  override val whiteSpace = """(\s|%.*)+""".r

  def termName: Parser[TermVar] = ident ^^ TermVar.apply
  def contName: Parser[ContVar] = ident ^^ ContVar.apply

  def primary: Parser[Term] =
    termName ^^ Var.apply |
    "(" ~> expr <~ ")"

  def continuation: Parser[Cont] =
    ("[" ~> contName <~ "]") ~ application ^^ { case c ~ a => Cont(Var(c), a) }

  def thunk: Parser[Thunk] =
    ("θ" | "?") ~> primary ^^ Thunk.apply

  def force: Parser[Force] =
    ("κ" | "!") ~> primary ^^ Force.apply

  def atom: Parser[Term] = continuation | thunk | force | primary

  def application: Parser[Term] = rep1(atom) ^^ (_.reduceLeft(Appl.apply))

  def lambda: Parser[Lam] =
    ("\\" | "λ") ~> termName ~ "." ~ expr ^^ { case p ~ _ ~ b => Lam(p, b) }

  def mu: Parser[Mu] =
    ("#" | "μ") ~> contName ~ "." ~ expr ^^ { case p ~ _ ~ b => Mu(p, b) }

  def expr: Parser[Term] = lambda | mu | application

  def parseExpr(input: String): Either[String, Term] =
    parseAll(expr, input) match
      case Success(result, _) => Right(result)
      case NoSuccess(msg, _) => Left(s"Parse error: $msg")
