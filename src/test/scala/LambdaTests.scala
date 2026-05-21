import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

class LambdaMuCalculusTest extends AnyFlatSpec with Matchers {

  def parse(s: String): Term = LambdaParser.parseExpr(s) match {
    case Right(expr) => expr
    case Left(err) => fail(s"Parse error: $err")
  }

  def shouldBeAlphaEq(e1: Term, e2: Term): Unit = {
    val result = e1.alphaEq(e2)
    if (!result) {
      println(s"Alpha equivalence FAILED!")
      println(s"Expression 1: ${e1.pretty}")
      println(s"Expression 2: ${e2.pretty}")
    }
    result shouldBe true
  }

  def freeTermVars(expr: Term): Set[TermVar] = expr.freeNames.collect {
    case tv: TermVar => tv
  }

  def freeContVars(expr: Term): Set[ContVar] = expr.freeNames.collect {
    case cv: ContVar => cv
  }

  "Alpha equivalence" should "recognize identical expressions" in {
    val expr = parse("λx.x")
    shouldBeAlphaEq(expr, expr)
  }

  it should "recognize alpha-equivalent lambda expressions" in {
    shouldBeAlphaEq(parse("λx.x"), parse("λy.y"))
  }

  it should "recognize alpha-equivalent mu expressions" in {
    shouldBeAlphaEq(parse("μα.[α] x"), parse("μβ.[β] x"))
  }

  it should "recognize alpha-equivalent thunk expressions" in {
    // θ(λx.x) and θ(λy.y) differ only in bound variable name
    shouldBeAlphaEq(parse("θ(λx.x)"), parse("θ(λy.y)"))
  }

  it should "recognize alpha-equivalent force expressions" in {
    // κ(λx.x) and κ(λy.y) differ only in bound variable name
    shouldBeAlphaEq(parse("κ(λx.x)"), parse("κ(λy.y)"))
  }

  it should "distinguish thunk from force" in {
    parse("θ(λx.x)").alphaEq(parse("κ(λx.x)")) shouldBe false
  }

  it should "distinguish different expressions" in {
    parse("λx.x").alphaEq(parse("λx.y")) shouldBe false
  }

  it should "handle nested bindings correctly" in {
    shouldBeAlphaEq(parse("λx.λy.x"), parse("λa.λb.a"))
  }

  "Beta reduction" should "perform simple beta reduction" in {
    parse("(λx.x) y").step shouldBe parse("y")
  }

  it should "perform beta reduction with substitution" in {
    parse("(λx.λy.x) a b").eval() shouldBe parse("a")
  }

  it should "avoid variable capture in beta reduction" in {
    // (λx.λy.x) y: substituting x → y inside λy, so y must be renamed
    parse("(λx.λy.x) y").step match {
      case Lam(param, body) =>
        param.name should not be "y"
        body shouldBe parse("y")
      case _ => fail("Expected lambda expression")
    }
  }

  it should "not evaluate the argument before substituting it" in {
    // (λx.y) Ω steps to y in one step; Ω is never evaluated
    val expr = parse("(λx.y) ((λx.x x) (λx.x x))")
    expr.step shouldBe parse("y")
  }

  "Mu reduction" should "perform mu reduction when continuation variable matches" in {
    parse("μα.[α] x").step shouldBe parse("x")
  }

  it should "not perform reduction when continuation variable doesn't match" in {
    val expr = parse("μα.[β] x")
    expr.step shouldBe expr
  }

  "Structural reduction" should "apply continuation to mu expression with same variable" in {
    // [α](μα.M) → M
    parse("[α] (μα.x)").step shouldBe parse("x")
  }

  it should "apply continuation to mu expression with different variable" in {
    // [α](μβ.x) → x[α/β]; since x doesn't contain β, result is x
    parse("[α] (μβ.x)").step shouldBe parse("x")
  }

  it should "apply continuation with proper substitution" in {
    // [α](μβ.[β] y) → [α] y  (substituting β → α in the body)
    parse("[α] (μβ.[β] y)").step shouldBe parse("[α] y")
  }

  "Thunk and Force operators" should "parse thunk expressions correctly" in {
    parse("θx") shouldBe a[Thunk]
    parse("?x") shouldBe a[Thunk]
  }

  it should "parse force expressions correctly" in {
    parse("κx") shouldBe a[Force]
    parse("!x") shouldBe a[Force]
  }

  it should "implement the basic κ(θ M) → M reduction rule" in {
    parse("κ(θx)").step shouldBe parse("x")
  }

  it should "implement thunk idempotency θ(θ M) ≡ θ M" in {
    // The smart constructor collapses θ(θM) to θM at construction time
    shouldBeAlphaEq(parse("θ(θx)"), parse("θx"))
  }

  it should "implement force idempotency κ(κ M) ≡ κ M" in {
    // The smart constructor collapses κ(κM) to κM at construction time
    shouldBeAlphaEq(parse("κ(κx)"), parse("κx"))
  }

  it should "not step inside a thunk" in {
    val omega = parse("(λx.x x) (λx.x x)")
    val thunkedOmega = Thunk(omega)
    thunkedOmega.step shouldBe thunkedOmega
  }

  it should "force evaluation of a thunk" in {
    val identity = parse("λx.x")
    Force(Thunk(identity)).step shouldBe identity
  }

  it should "handle nested thunk/force operations" in {
    parse("κ(θ(λx.x))").step shouldBe parse("λx.x")
  }

  it should "expose an unreduced redex after forcing" in {
    // κ(θ((λx.x) y)) → (λx.x) y, which still has a beta redex
    val result = parse("κ(θ((λx.x) y))").step
    result shouldBe parse("(λx.x) y")
    result.step shouldBe parse("y")
  }

  "Infinite Ones Stream" should "step F F to a pair with head one and a thunk tail" in {
    val one  = parse("λf.λx.f x")
    val pair = parse("λa.λb.λc.c a b")
    val F = Lam(TermVar("x"),
      Appl(Appl(pair, one), Thunk(Appl(Var(TermVar("x")), Var(TermVar("x"))))))

    Appl(F, F).step match {
      case Appl(Appl(_, headVal), _: Thunk) => shouldBeAlphaEq(headVal, one)
      case other => fail(s"Expected pair one (θ(...)), got: ${other.pretty}")
    }
  }

  it should "keep the tail suspended in a thunk" in {
    val one  = parse("λf.λx.f x")
    val pair = parse("λa.λb.λc.c a b")
    val F = Lam(TermVar("x"),
      Appl(Appl(pair, one), Thunk(Appl(Var(TermVar("x")), Var(TermVar("x"))))))

    Appl(F, F).step match {
      case Appl(_, thunk: Thunk) =>
        thunk.term match {
          case Appl(f1, f2) =>
            shouldBeAlphaEq(f1, F)
            shouldBeAlphaEq(f2, F)
          case _ => fail("Expected F F inside thunk")
        }
      case other => fail(s"Expected pair structure, got: ${other.pretty}")
    }
  }

  it should "allow lazy access to head and tail" in {
    val one  = parse("λf.λx.f x")
    val pair = parse("λa.λb.λc.c a b")
    val fst  = parse("λa.λb.a")
    val snd  = parse("λa.λb.b")
    val F = Lam(TermVar("x"),
      Appl(Appl(pair, one), Thunk(Appl(Var(TermVar("x")), Var(TermVar("x"))))))

    val ones = Appl(F, F).step

    // head is one
    shouldBeAlphaEq(Appl(ones, fst).eval(), one)

    // tail is a thunk; forcing it produces another pair whose head is also one
    val tail = Appl(ones, snd).eval()
    tail shouldBe a[Thunk]
    val nextOnes = Force(tail.asInstanceOf[Thunk]).step
    shouldBeAlphaEq(Appl(nextOnes, fst).eval(), one)
  }

  "Lazy Infinite Zeros Stream" should "evaluate F F without looping" in {
    val zero = parse("λf.λx.x")
    val pair = parse("λa.λb.λc.c a b")
    val F = parse("λx.pair zero (?(x x))").subst(Map(
      TermVar("pair") -> pair,
      TermVar("zero") -> zero
    ))

    // Full evaluation should terminate and produce a weak-head normal form (a lambda)
    val evaluated = Appl(F, F).eval(maxSteps = 100)
    evaluated shouldBe a[Lam]

    // Head of the evaluated stream should be zero
    shouldBeAlphaEq(Appl(evaluated, parse("λa.λb.a")).eval(), zero)
  }

  it should "create infinite stream via self-application F F" in {
    val zero = parse("λf.λx.x")
    val pair = parse("λa.λb.λc.c a b")
    val F = Lam(TermVar("x"),
      Appl(Appl(pair, zero), Thunk(Appl(Var(TermVar("x")), Var(TermVar("x"))))))

    Appl(F, F).step match {
      case Appl(Appl(_, headValue), tailThunk: Thunk) =>
        shouldBeAlphaEq(headValue, zero)
        tailThunk.term match {
          case Appl(f1, f2) =>
            shouldBeAlphaEq(f1, F)
            shouldBeAlphaEq(f2, F)
          case _ => fail("Expected F F inside thunk")
        }
      case other => fail(s"Expected pair zero (θ(F F)), got: ${other.pretty}")
    }
  }

  it should "allow lazy access to stream elements" in {
    val zero = parse("λf.λx.x")
    val pair = parse("λa.λb.λc.c a b")
    val fst  = parse("λa.λb.a")
    val snd  = parse("λa.λb.b")
    val F = Lam(TermVar("x"),
      Appl(Appl(pair, zero), Thunk(Appl(Var(TermVar("x")), Var(TermVar("x"))))))

    val zeros = Appl(F, F).step

    shouldBeAlphaEq(Appl(zeros, fst).eval(), zero)

    val tail = Appl(zeros, snd).eval()
    tail shouldBe a[Thunk]

    val nextZeros = Force(tail.asInstanceOf[Thunk]).step
    nextZeros shouldBe a[Appl]
    shouldBeAlphaEq(Appl(nextZeros, fst).eval(), zero)
  }

  it should "demonstrate infinite lazy unfolding" in {
    val zero = parse("λf.λx.x")
    val pair = parse("λa.λb.λc.c a b")
    val fst  = parse("λa.λb.a")
    val snd  = parse("λa.λb.b")
    val F = Lam(TermVar("x"),
      Appl(Appl(pair, zero), Thunk(Appl(Var(TermVar("x")), Var(TermVar("x"))))))

    val zeros = Appl(F, F).step

    def getNthElement(stream: Term, n: Int): Term =
      if n == 0 then Appl(stream, fst).eval()
      else
        val tail = Appl(stream, snd).eval().asInstanceOf[Thunk]
        getNthElement(Force(tail).step, n - 1)

    for i <- 0 until 5 do
      shouldBeAlphaEq(getNthElement(zeros, i), zero)
  }

  it should "work with the REPL session file format" in {
    val environment: Map[Name, Term] = Map(
      TermVar("zero") -> parse("λf.λx.x"),
      TermVar("pair") -> parse("λa.λb.λc.c a b"),
      TermVar("fst")  -> parse("λa.λb.a"),
      TermVar("snd")  -> parse("λa.λb.b")
    )
    val F = parse("λx.pair zero (?(x x))").subst(environment)
    val evaluated = Appl(F, F).eval()
    evaluated shouldBe a[Lam]
    shouldBeAlphaEq(Appl(evaluated, parse("λa.λb.a")).eval(), parse("λf.λx.x"))
  }

  "Free variables" should "identify free term variables correctly" in {
    freeTermVars(parse("x"))      shouldBe Set(TermVar("x"))
    freeTermVars(parse("λx.x"))   shouldBe Set.empty
    freeTermVars(parse("λx.y"))   shouldBe Set(TermVar("y"))
    freeTermVars(parse("λx.x y")) shouldBe Set(TermVar("y"))
  }

  it should "identify free continuation variables correctly" in {
    freeContVars(parse("x"))           shouldBe Set.empty
    freeContVars(parse("[α] x"))       shouldBe Set(ContVar("α"))
    freeContVars(parse("μα.x"))        shouldBe Set.empty
    freeContVars(parse("μα.[β] x"))    shouldBe Set(ContVar("β"))
    freeContVars(parse("μα.[α] x"))    shouldBe Set.empty
  }

  it should "handle free variables in thunk and force expressions" in {
    freeTermVars(parse("θx"))       shouldBe Set(TermVar("x"))
    freeTermVars(parse("κx"))       shouldBe Set(TermVar("x"))
    freeTermVars(parse("θ(λx.y)"))  shouldBe Set(TermVar("y"))
    freeContVars(parse("θ([α] x)")) shouldBe Set(ContVar("α"))
  }

  "Substitution" should "substitute free variables" in {
    parse("x").subst(Map(TermVar("x") -> parse("y"))) shouldBe parse("y")
  }

  it should "not substitute bound variables" in {
    val result = parse("λx.x").subst(Map(TermVar("x") -> parse("y")))
    shouldBeAlphaEq(result, parse("λx.x"))
  }

  it should "avoid variable capture" in {
    // Substituting x → y in λy.x: the bound y must be renamed
    parse("λy.x").subst(Map(TermVar("x") -> parse("y"))) match {
      case Lam(param, body) =>
        param.name should not be "y"
        body shouldBe parse("y")
      case _ => fail("Expected lambda expression")
    }
  }

  it should "substitute in thunk and force expressions" in {
    parse("θx").subst(Map(TermVar("x") -> parse("y"))) shouldBe parse("θy")
    parse("κx").subst(Map(TermVar("x") -> parse("y"))) shouldBe parse("κy")
  }

  "Lazy evaluation vs Normalization" should "show the difference" in {
    // succ 1: (λn.λf.λx.f (n f x)) (λf.λx.f x)
    val expr = parse("(λn.λf.λx.f (n f x)) (λf.λx.f x)")

    // eval does one beta step then stops — the inner redex is still unreduced
    val lazyResult = expr.eval()
    shouldBeAlphaEq(lazyResult, parse("λf.λx.f ((λf.λx.f x) f x)"))

    // normalize reduces the inner redex too, yielding Church numeral 2
    shouldBeAlphaEq(lazyResult.normalize(), parse("λf.λx.f (f x)"))
  }

  "Normalization" should "reduce inside lambda bodies" in {
    parse("λf.f ((λx.x) y)").normalize() shouldBe parse("λf.f y")
  }

  it should "reduce inside application arguments" in {
    parse("f ((λx.x) y)").normalize() shouldBe parse("f y")
  }

  it should "handle nested reductions" in {
    parse("λf.λx.f ((λy.y) x)").normalize() shouldBe parse("λf.λx.f x")
  }

  it should "work with mu expressions in reduction context" in {
    parse("μα.[α] x").normalize() shouldBe parse("x")
  }

  it should "preserve mu expressions not in reduction context" in {
    parse("λf.f (μα.[β] x)").normalize() shouldBe parse("λf.f (μα.[β] x)")
  }

  it should "reduce structural congruence during normalization" in {
    parse("λf.[α] (μβ.[β] x)").normalize() shouldBe parse("λf.[α] x")
  }

  it should "not change expressions already in normal form" in {
    val expr = parse("λf.λx.f x")
    expr.normalize() shouldBe expr
  }

  it should "normalize thunk and force expressions" in {
    parse("λf.f (κ(θ((λx.x) y)))").normalize() shouldBe parse("λf.f y")
  }

  "Standard reduction rules" should "cover all four reduction types" in {
    // β: (λx.M) N → M[N/x]
    parse("(λx.x) y").step shouldBe parse("y")

    // μ: μα.[α] M → M
    parse("μα.[α] x").step shouldBe parse("x")

    // Structural: [α](μβ.[β] y) → [α] y
    parse("[α] (μβ.[β] y)").step shouldBe parse("[α] y")

    // θ/κ: κ(θ M) → M
    parse("κ(θx)").step shouldBe parse("x")
  }

  "Classical logic features" should "demonstrate double negation elimination" in {
    val dne         = parse("λx.μα.x (λy.[α] y)")
    val doubleNegPf = parse("λf.f z")
    Appl(dne, doubleNegPf).eval() shouldBe parse("z")
  }

  it should "demonstrate Peirce's law with correct expectations" in {
    val peirce       = parse("λf.μα.f (λx.[α] x)")
    val testFunction = parse("λg.μβ.[α] b")  // α is FREE here

    Appl(peirce, testFunction).eval() match {
      case Mu(outerParam, Mu(innerParam, Cont(Var(ContVar(freeAlpha)), Var(TermVar("b"))))) =>
        // outer μ got a fresh name to avoid capturing the free α
        innerParam.name shouldBe "β"
        freeAlpha should not be outerParam.name
        freeAlpha shouldBe "α"
      case other =>
        fail(s"Expected μ_.μβ.[α] b structure, got: ${other.pretty}")
    }
  }

  "Complex expressions" should "handle function composition" in {
    val result = parse("(λf.λg.λx.f (g x)) (λy.y) (λz.z)").eval().normalize()
    shouldBeAlphaEq(result, parse("λx.x"))
  }

  it should "handle mixed lambda-mu expressions" in {
    parse("(λx.μα.[α] x) (f y)").eval() shouldBe parse("f y")
  }

  it should "handle mixed lambda-mu-thunk-force expressions" in {
    parse("(λx.κ(θx)) (f y)").eval() shouldBe parse("f y")
  }

  "Pretty printing" should "handle parentheses correctly" in {
    parse("(λx.x) y").pretty   shouldBe "(λx.x) y"
    parse("f (g h)").pretty    shouldBe "f (g h)"
    parse("[α] (λx.x)").pretty shouldBe "[α] (λx.x)"
    parse("λx.(x y)").pretty   shouldBe "λx.x y"
  }

  it should "parenthesize lambda and mu when they appear as arguments" in {
    // These round-trips would silently break if the argument weren't parenthesized
    parse("f (λx.x)").pretty shouldBe "f (λx.x)"
    parse("f (μα.x)").pretty shouldBe "f (μα.x)"
  }

  it should "print mu expressions correctly" in {
    parse("μα.[α] x").pretty  shouldBe "μα.[α] x"
    parse("(μα.x) y").pretty  shouldBe "(μα.x) y"
  }

  it should "print thunk and force expressions correctly" in {
    parse("θx").pretty     shouldBe "θx"
    parse("κx").pretty     shouldBe "κx"
    parse("θ(x y)").pretty shouldBe "θ(x y)"
    parse("κ(x y)").pretty shouldBe "κ(x y)"
  }

  "Evaluation termination" should "terminate on normalizing expressions" in {
    parse("(λx.x) y").eval() shouldBe parse("y")
  }

  it should "stop after maxSteps on non-terminating expressions" in {
    val omega = parse("(λx.x x) (λx.x x)")
    val result = omega.eval(maxSteps = 10)
    // omega reduces to itself every step, so result is alpha-equivalent to omega
    result shouldBe a[Appl]
    shouldBeAlphaEq(result, omega)
  }

  it should "not evaluate unused arguments" in {
    val omega = parse("(λx.x x) (λx.x x)")
    Appl(parse("λx.y"), omega).eval(maxSteps = 5) shouldBe parse("y")
  }

  it should "demonstrate thunks prevent infinite loops" in {
    val omega        = parse("(λx.x x) (λx.x x)")
    val thunkedOmega = Thunk(omega)
    thunkedOmega.eval(maxSteps = 5) shouldBe thunkedOmega
    Force(thunkedOmega).step shouldBe omega
  }

  "Recursive structures with thunks" should "demonstrate self-application without infinite loops" in {
    val F        = parse("λx.θ(x x)")
    val selfAppl = Appl(F, F)
    selfAppl.step match {
      case Thunk(inner) => shouldBeAlphaEq(inner, selfAppl)
      case other        => fail(s"Expected thunk, got: ${other.pretty}")
    }
  }

  it should "allow controlled unfolding via force" in {
    val F        = parse("λx.θ(x x)")
    val selfAppl = Appl(F, F)
    val thunked  = selfAppl.step.asInstanceOf[Thunk]
    shouldBeAlphaEq(Force(thunked).step, selfAppl)
  }
}
