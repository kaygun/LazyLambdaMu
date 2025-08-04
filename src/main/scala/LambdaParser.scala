import scala.util.parsing.combinator.JavaTokenParsers

object LambdaParser extends JavaTokenParsers:
  // Handle comments starting with %
  override def skipWhitespace = true
  override val whiteSpace = """(\s|%.*)+""".r
  
  // Direct name parsers - no need to wrap in Var here
  def termName: Parser[TermVar] = ident ^^ TermVar.apply
  def contName: Parser[ContVar] = ident ^^ ContVar.apply

  // Primary expressions: term variables, parenthesized expressions
  def primary: Parser[Term] =
    termName ^^ Var.apply |
    "(" ~> expr <~ ")"

  // Continuations: [α] M where α is a continuation variable
  def continuation: Parser[Cont] =
    "[" ~> contName ~ "]" ~ application ^^ { case c ~ _ ~ a => Cont(Var(c), a) }

  // Thunk: θM or ?M (suspends evaluation)
  def thunk: Parser[Thunk] =
    ("θ" | "?") ~> primary ^^ Thunk.apply

  // Force: κM or !M (forces evaluation of thunks)
  def force: Parser[Force] =
    ("κ" | "!") ~> primary ^^ Force.apply

  // Atoms: primary expressions, continuations, thunks, and force
  def atom: Parser[Term] = continuation | thunk | force | primary

  // Applications: left associative sequence of atoms
  def application: Parser[Term] = rep1(atom) ^^ (_.reduceLeft(Appl.apply))

  // Lambda abstraction: λx.M
  def lambda: Parser[Lam] =
    ("\\" | "λ") ~> termName ~ "." ~ expr ^^ {
      case p ~ _ ~ b => Lam(p, b)
    }

  // Mu abstraction: μα.M
  def mu: Parser[Mu] =
    ("#" | "μ") ~> contName ~ "." ~ expr ^^ {
      case p ~ _ ~ b => Mu(p, b)
    }

  def expr: Parser[Term] = lambda | mu | application

  def parseExpr(input: String): Either[String, Term] =
    parseAll(expr, input) match
      case Success(result, _) => Right(result)
      case NoSuccess(msg, _) => Left(s"Parse error: $msg")
