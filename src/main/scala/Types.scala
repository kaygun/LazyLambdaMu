sealed trait Name {
  def name: String
}
case class TermVar(name: String) extends Name
case class ContVar(name: String) extends Name

sealed trait Term:
  def pretty: String = prettyWithDepth(0)
  def prettyWithDepth(depth: Int): String
  def freeNames: Set[Name]
  def alphaEq(that: Term, env: Map[Name, Name] = Map.empty): Boolean
  def subst(substMap: Map[Name, Term]): Term
  def step: Term = reduction.getOrElse(this)
  def reduction: Option[Term] = None
  def eval(maxSteps: Int = 1000): Term =
    @annotation.tailrec
    def loop(current: Term, count: Int): Term =
      if count >= maxSteps then current
      else
        val next = current.step
        if next.alphaEq(current) then current
        else loop(next, count + 1)
    loop(this, 0)

  def normalize(): Term = normalizeWithDepth(0)
  def normalizeWithDepth(depth: Int): Term = this

object Term:
  private var counter = 0
  def fresh(prefix: String = "_"): String =
    counter += 1
    s"$prefix$counter"

abstract class Binding(val param: Name, val body: Term) extends Term:
  def freeNames = body.freeNames - param
  override def alphaEq(that: Term, env: Map[Name, Name] = Map.empty) = that match
    case other: Binding if other.getClass == this.getClass =>
      body.alphaEq(other.body, env + (param -> other.param))
    case _ => false
  def subst(substMap: Map[Name, Term]) =
    val (p, prepared) =
      if substMap.values.exists(_.freeNames.contains(param)) then
        val fresh = freshParam()
        (fresh, body.subst(Map(param -> Var(fresh))))
      else (param, body)
    reconstruct(p, prepared.subst(substMap - param))
  override def step = reduction.getOrElse {
    body.step match
      case b if !b.alphaEq(body) => reconstruct(param, b)
      case _ => this
  }
  override def normalizeWithDepth(depth: Int) =
    if depth > 50 then this
    else
      val normBody = body.normalizeWithDepth(depth + 1)
      val candidate = reconstruct(param, normBody)
      val stepped = candidate.step
      if !stepped.alphaEq(candidate) then stepped.normalizeWithDepth(depth + 1) else candidate

  protected def freshParam(): Name
  protected def reconstruct(param: Name, body: Term): Binding

abstract class Application(val head: Term, val arg: Term) extends Term:
  def freeNames = head.freeNames ++ arg.freeNames
  override def alphaEq(that: Term, env: Map[Name, Name] = Map.empty) = that match
    case other: Application if other.getClass == this.getClass =>
      head.alphaEq(other.head, env) && arg.alphaEq(other.arg, env)
    case _ => false
  def subst(substMap: Map[Name, Term]) = reconstruct(head.subst(substMap), arg.subst(substMap))
  override def normalizeWithDepth(depth: Int) =
    if depth > 50 then this
    else
      val normH = head.normalizeWithDepth(depth + 1)
      val normA = arg.normalizeWithDepth(depth + 1)
      val candidate = reconstruct(normH, normA)
      val stepped = candidate.step
      if !stepped.alphaEq(candidate) then stepped.normalizeWithDepth(depth + 1) else candidate

  protected def reconstruct(head: Term, arg: Term): Application

abstract class Unary(val term: Term) extends Term:
  protected def symbol: String
  def prettyWithDepth(depth: Int) =
    if depth > 10 then s"$symbol(...)"
    else term match
      case _: Appl | _: Cont => s"$symbol(${term.prettyWithDepth(depth + 1)})"
      case _ => s"$symbol${term.prettyWithDepth(depth + 1)}"
  def freeNames = term.freeNames
  override def alphaEq(that: Term, env: Map[Name, Name] = Map.empty) = that match
    case other: Unary if other.getClass == this.getClass =>
      term.alphaEq(other.term, env)
    case _ => false
  def subst(substMap: Map[Name, Term]) = reconstruct(term.subst(substMap))
  override def step = reduction.getOrElse {
    val newTerm = term.step
    if !newTerm.alphaEq(term) then reconstruct(newTerm) else this
  }
  override def normalizeWithDepth(depth: Int) =
    if depth > 50 then this
    else
      val normTerm = term.normalizeWithDepth(depth + 1)
      val candidate = reconstruct(normTerm)
      val stepped = candidate.step
      if !stepped.alphaEq(candidate) then stepped.normalizeWithDepth(depth + 1) else candidate

  protected def reconstruct(term: Term): Unary

case class Var(n: Name) extends Term:
  def prettyWithDepth(depth: Int) = n.name
  override def alphaEq(that: Term, env: Map[Name, Name] = Map.empty) = that match
    case Var(m) => env.getOrElse(n, n) == env.getOrElse(m, m)
    case _ => false
  def freeNames = Set(n)
  def subst(substMap: Map[Name, Term]) = substMap.getOrElse(n, this)

case class Lam(override val param: TermVar, override val body: Term) extends Binding(param, body):
  def prettyWithDepth(depth: Int) = s"λ${param.name}.${body.prettyWithDepth(depth)}"
  protected def freshParam() = TermVar(Term.fresh(param.name))
  protected def reconstruct(param: Name, body: Term) = Lam(param.asInstanceOf[TermVar], body)

case class Mu(override val param: ContVar, override val body: Term) extends Binding(param, body):
  def prettyWithDepth(depth: Int) = s"μ${param.name}.${body.prettyWithDepth(depth)}"
  protected def freshParam() = ContVar(Term.fresh(param.name))
  protected def reconstruct(param: Name, body: Term) = Mu(param.asInstanceOf[ContVar], body)
  override def reduction = body match
    case Cont(Var(c: ContVar), x) if c == param => Some(x)
    case _ => None

case class Appl(override val head: Term, override val arg: Term) extends Application(head, arg):
  def prettyWithDepth(depth: Int) =
    val headStr = head match
      case _: Lam | _: Mu => s"(${head.prettyWithDepth(depth)})"
      case _ => head.prettyWithDepth(depth)
    val argStr = arg match
      case _: Appl | _: Lam | _: Mu => s"(${arg.prettyWithDepth(depth)})"
      case _ => arg.prettyWithDepth(depth)
    s"$headStr $argStr"
  protected def reconstruct(head: Term, arg: Term) = Appl(head, arg)
  override def step = head match
    case Lam(x, b) => b.subst(Map(x -> arg))
    case _ =>
      val newHead = head.step
      if !newHead.alphaEq(head) then Appl(newHead, arg) else this

case class Cont(override val head: Term, override val arg: Term) extends Application(head, arg):
  def prettyWithDepth(depth: Int) =
    val argStr = arg match
      case _: Lam | _: Mu => s"(${arg.prettyWithDepth(depth)})"
      case _ => arg.prettyWithDepth(depth)
    s"[${head.prettyWithDepth(depth)}] $argStr"
  protected def reconstruct(head: Term, arg: Term) = Cont(head, arg)
  override def reduction = (head, arg) match
    case (Var(c2: ContVar), Mu(c1, b)) =>
      Some(if c1 == c2 then b else b.subst(Map[Name, Term](c1 -> Var(c2))))
    case _ => None
  override def step = reduction.getOrElse {
    val newHead = head.step
    if !newHead.alphaEq(head) then Cont(newHead, arg) else this
  }

case class Thunk(override val term: Term) extends Unary(term):
  protected def symbol = "θ"
  protected def reconstruct(term: Term) = Thunk.apply(term)
  override def step = this

object Thunk:
  def apply(term: Term): Thunk = term match
    case t: Thunk => t
    case _ => new Thunk(term)

case class Force(override val term: Term) extends Unary(term):
  protected def symbol = "κ"
  protected def reconstruct(term: Term) = Force.apply(term)
  override def reduction = term match
    case Thunk(m) => Some(m)
    case _ => None

object Force:
  def apply(term: Term): Force = term match
    case f: Force => f
    case _ => new Force(term)
