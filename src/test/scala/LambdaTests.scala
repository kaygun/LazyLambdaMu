import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

class LambdaMuCalculusTest extends AnyFlatSpec with Matchers {

  // Helper to parse expressions for testing
  def parse(s: String): Term = LambdaParser.parseExpr(s) match {
    case Right(expr) => expr
    case Left(err) => fail(s"Parse error: $err")
  }

  // Helper to check if two expressions are alpha-equivalent
  def shouldBeAlphaEq(e1: Term, e2: Term): Unit = {
    val result = e1.alphaEq(e2)
    if (!result) {
      println(s"Alpha equivalence FAILED!")
      println(s"Expression 1: ${e1.pretty}")
      println(s"Expression 2: ${e2.pretty}")
    }
    result shouldBe true
  }

  // Helper to get free term variables
  def freeTermVars(expr: Term): Set[TermVar] = expr.freeNames.collect {
    case tv: TermVar => tv
  }

  // Helper to get free continuation variables  
  def freeContVars(expr: Term): Set[ContVar] = expr.freeNames.collect {
    case cv: ContVar => cv
  }

  "Alpha equivalence" should "recognize identical expressions" in {
    val expr = parse("λx.x")
    shouldBeAlphaEq(expr, expr)
  }

  it should "recognize alpha-equivalent lambda expressions" in {
    val e1 = parse("λx.x")
    val e2 = parse("λy.y")
    shouldBeAlphaEq(e1, e2)
  }

  it should "recognize alpha-equivalent mu expressions" in {
    val e1 = parse("μα.[α] x")
    val e2 = parse("μβ.[β] x")
    shouldBeAlphaEq(e1, e2)
  }

  it should "recognize alpha-equivalent thunk expressions" in {
    val e1 = parse("θx")
    val e2 = parse("θx")
    shouldBeAlphaEq(e1, e2)
  }

  it should "recognize alpha-equivalent force expressions" in {
    val e1 = parse("κx")
    val e2 = parse("κx")
    shouldBeAlphaEq(e1, e2)
  }

  it should "distinguish different expressions" in {
    val e1 = parse("λx.x")
    val e2 = parse("λx.y")
    e1.alphaEq(e2) shouldBe false
  }

  it should "handle nested bindings correctly" in {
    val e1 = parse("λx.λy.x")
    val e2 = parse("λa.λb.a")
    shouldBeAlphaEq(e1, e2)
  }

  "Beta reduction" should "perform simple beta reduction" in {
    val expr = parse("(λx.x) y")
    val result = expr.step
    result shouldBe parse("y")
  }

  it should "perform beta reduction with substitution" in {
    val expr = parse("(λx.λy.x) a b")
    val result = expr.eval()
    result shouldBe parse("a")
  }

  it should "avoid variable capture in beta reduction" in {
    val expr = parse("(λx.λy.x) y")
    val result = expr.step
    result match {
      case Lam(param, body) => 
        param.name should not be "y"  // bound variable renamed
        body shouldBe parse("y")       // still refers to free y
      case _ => fail("Expected lambda expression")
    }
  }

  it should "demonstrate lazy evaluation - arguments not evaluated until needed" in {
    // In lazy evaluation: (λx.y) (infinite_loop) should return y without evaluating infinite_loop
    val expr = parse("(λx.y) ((λx.x x) (λx.x x))")  // (λx.y) applied to omega
    val result = expr.step  // Should step to y without evaluating omega
    result shouldBe parse("y")
  }

  "Mu reduction" should "perform mu reduction when continuation variable matches" in {
    val expr = parse("μα.[α] x")
    val result = expr.step
    result shouldBe parse("x")
  }

  it should "not perform reduction when continuation variable doesn't match" in {
    val expr = parse("μα.[β] x")
    val result = expr.step
    result shouldBe expr  // Should not reduce
  }

  "Structural reduction" should "apply continuation to mu expression with same variable" in {
    val expr = parse("[α] (μα.x)")
    val result = expr.step
    result shouldBe parse("x")
  }

  it should "apply continuation to mu expression with different variable" in {
    val expr = parse("[α] (μβ.x)")
    val result = expr.step
    result shouldBe parse("x")
  }

  it should "apply continuation with proper substitution" in {
    val expr = parse("[α] (μβ.[β] y)")
    val result = expr.step
    result shouldBe parse("[α] y")
  }

  "Thunk and Force operators" should "parse thunk expressions correctly" in {
    val expr1 = parse("θx")
    val expr2 = parse("?x")
    expr1 shouldBe a[Thunk]
    expr2 shouldBe a[Thunk]
  }

  it should "parse force expressions correctly" in {
    val expr1 = parse("κx")
    val expr2 = parse("!x")
    expr1 shouldBe a[Force]
    expr2 shouldBe a[Force]
  }

  it should "implement the basic κ(θ M) → M reduction rule" in {
    val thunked = parse("θx")
    val forced = parse("κ(θx)")
    val result = forced.step
    result shouldBe parse("x")
  }

  it should "implement thunk idempotency θ(θ M) ≡ θ M" in {
    val doubleThunk = parse("θ(θx)")
    val singleThunk = parse("θx")
    shouldBeAlphaEq(doubleThunk, singleThunk)
  }

  it should "implement force idempotency κ(κ M) ≡ κ M" in {
    val doubleForce = parse("κ(κx)")
    val singleForce = parse("κx")
    shouldBeAlphaEq(doubleForce, singleForce)
  }

  it should "suspend evaluation in thunks" in {
    val omega = parse("(λx.x x) (λx.x x)")
    val thunkedOmega = Thunk(omega)
    // Thunk should not reduce its contents
    thunkedOmega.step shouldBe thunkedOmega
  }

  it should "force evaluation of thunks only when needed" in {
    val identity = parse("λx.x")
    val thunked = Thunk(identity)
    val forced = Force(thunked)
    
    forced.step shouldBe identity
  }

  it should "handle nested thunk/force operations" in {
    val expr = parse("κ(θ(λx.x))")
    val result = expr.step
    result shouldBe parse("λx.x")
  }

  it should "work with complex expressions" in {
    val expr = parse("κ(θ((λx.x) y))")
    val result = expr.step
    result shouldBe parse("(λx.x) y")
    
    // Further evaluation should do beta reduction
    val fullyReduced = result.step
    fullyReduced shouldBe parse("y")
  }

  "Infinite Ones Stream" should "construct the recursive F function correctly" in {
    // F := λx.pair zero (θ(x x))
    val zero = parse("λf.λx.x")  // Church numeral 0
    val pair = parse("λa.λb.λc.c a b")  // Pair constructor
    
    // Manually construct F for testing
    val F = Lam(TermVar("x"), 
      Appl(
        Appl(pair, zero),
        Thunk(Appl(Var(TermVar("x")), Var(TermVar("x"))))
      ))
    
    F shouldBe a[Lam]
    F.body shouldBe a[Appl]
  }

  it should "create the ones stream via F F" in {
    val zero = parse("λf.λx.x")
    val pair = parse("λa.λb.λc.c a b")
    val F = Lam(TermVar("x"), 
      Appl(
        Appl(pair, zero),
        Thunk(Appl(Var(TermVar("x")), Var(TermVar("x"))))
      ))
    
    val ones = Appl(F, F)
    ones shouldBe a[Appl]
    
    // F F should reduce to pair zero (θ(F F))
    val stepped = ones.step
    stepped match {
      case Appl(Appl(pairFn, zeroVal), thunk: Thunk) =>
        shouldBeAlphaEq(zeroVal, zero)
        thunk shouldBe a[Thunk]
      case _ => fail(s"Expected pair structure, got: ${stepped.pretty}")
    }
  }

  it should "demonstrate lazy stream access" in {
    // Simplified test using variables for pair components
    val fst = parse("λa.λb.a")
    val snd = parse("λa.λb.b")
    
    // Create a mock ones stream: λc.c zero (θ(...))
    val zero = parse("λf.λx.x")
    val mockThunk = Thunk(parse("x"))  // Simplified thunk
    val mockOnes = Lam(TermVar("c"), 
      Appl(Appl(Var(TermVar("c")), zero), mockThunk))
    
    // Extract head: ones fst
    val head = Appl(mockOnes, fst)
    val headResult = head.eval()
    shouldBeAlphaEq(headResult, zero)
    
    // Extract tail: ones snd
    val tail = Appl(mockOnes, snd)
    val tailResult = tail.eval()
    tailResult shouldBe mockThunk
  }

  "Lazy Infinite Zeros Stream" should "construct without infinite loops" in {
    // Test the actual zeros stream as described in simple_ones.txt
    val zero = parse("λf.λx.x")
    val pair = parse("λa.λb.λc.c a b")
    val F = parse("λx.pair zero (?(x x))")
    
    // Resolve pair and zero in F's body
    val resolvedF = F.subst(Map(
      TermVar("pair") -> pair,
      TermVar("zero") -> zero
    ))
    
    resolvedF shouldBe a[Lam]
  }

  it should "create infinite stream via self-application F F" in {
    val zero = parse("λf.λx.x")
    val pair = parse("λa.λb.λc.c a b")
    
    // F := λx. pair zero (θ(x x))
    val F = Lam(TermVar("x"), 
      Appl(
        Appl(pair, zero),
        Thunk(Appl(Var(TermVar("x")), Var(TermVar("x"))))
      ))
    
    // zeros := F F
    val zeros = Appl(F, F)
    
    // This should reduce to: pair zero (θ(F F)) without infinite loops
    val stepped = zeros.step
    stepped shouldBe a[Appl]
    
    stepped match {
      case Appl(Appl(pairConstructor, headValue), tailThunk: Thunk) =>
        // Head should be zero
        shouldBeAlphaEq(headValue, zero)
        
        // Tail should be a thunk containing F F (the same structure)
        tailThunk shouldBe a[Thunk]
        
        // The thunk should contain the original F F expression
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
    val fst = parse("λa.λb.a")
    val snd = parse("λa.λb.b")
    
    val F = Lam(TermVar("x"), 
      Appl(
        Appl(pair, zero),
        Thunk(Appl(Var(TermVar("x")), Var(TermVar("x"))))
      ))
    
    val zeros = Appl(F, F).step  // Get pair zero (θ(F F))
    
    // Extract head: zeros fst
    val headAccess = Appl(zeros, fst)
    val headResult = headAccess.eval()
    shouldBeAlphaEq(headResult, zero)
    
    // Extract tail: zeros snd  
    val tailAccess = Appl(zeros, snd)
    val tailResult = tailAccess.eval()
    tailResult shouldBe a[Thunk]
    
    // Force the tail to get the next element
    val forcedTail = Force(tailResult.asInstanceOf[Thunk])
    val nextZeros = forcedTail.step
    
    // The forced tail should give us another pair zero (θ(...))
    nextZeros shouldBe a[Appl]
    
    // Get head of the tail (should also be zero)
    val tailHead = Appl(nextZeros, fst)
    val tailHeadResult = tailHead.eval()
    shouldBeAlphaEq(tailHeadResult, zero)
  }

  it should "demonstrate infinite lazy unfolding" in {
    val zero = parse("λf.λx.x")
    val pair = parse("λa.λb.λc.c a b")
    val fst = parse("λa.λb.a")
    val snd = parse("λa.λb.b")
    
    val F = Lam(TermVar("x"), 
      Appl(
        Appl(pair, zero),
        Thunk(Appl(Var(TermVar("x")), Var(TermVar("x"))))
      ))
    
    val zeros = Appl(F, F).step
    
    // Access multiple elements by forcing tails repeatedly
    def getNthElement(stream: Term, n: Int): Term = {
      if n == 0 then
        // Get head: stream fst
        Appl(stream, fst).eval()
      else
        // Get tail, force it, then recurse: !(stream snd)
        val tail = Appl(stream, snd).eval().asInstanceOf[Thunk]
        val forcedTail = Force(tail).step
        getNthElement(forcedTail, n - 1)
    }
    
    // Test first few elements are all zero
    for i <- 0 until 3 do
      val element = getNthElement(zeros, i)
      shouldBeAlphaEq(element, zero)
  }

  it should "work with the REPL session file format" in {
    // Test that our stream works with the format from simple_ones.txt
    val environment: Map[Name, Term] = Map(
      TermVar("zero") -> parse("λf.λx.x"),
      TermVar("pair") -> parse("λa.λb.λc.c a b"),
      TermVar("fst") -> parse("λa.λb.a"),
      TermVar("snd") -> parse("λa.λb.b")
    )
    
    // F := λx.pair zero (?(x x)) with variables resolved
    val F = parse("λx.pair zero (?(x x))").subst(environment)
    
    // zeros := F F
    val zeros = Appl(F, F)
    
    // This should evaluate without infinite loops
    val evaluated = zeros.eval()
    evaluated shouldBe a[Lam]  // Should be λc.c zero (θ(...))
    
    // Should be able to extract head
    val fst = parse("λa.λb.a")
    val headAccess = Appl(evaluated, fst)
    val head = headAccess.eval()
    
    shouldBeAlphaEq(head, parse("λf.λx.x"))  // Should be zero
  }

  "Free variables" should "identify free term variables correctly" in {
    freeTermVars(parse("x")) shouldBe Set(TermVar("x"))
    freeTermVars(parse("λx.x")) shouldBe Set.empty
    freeTermVars(parse("λx.y")) shouldBe Set(TermVar("y"))
    freeTermVars(parse("λx.x y")) shouldBe Set(TermVar("y"))
  }

  it should "identify free continuation variables correctly" in {
    freeContVars(parse("x")) shouldBe Set.empty
    freeContVars(parse("[α] x")) shouldBe Set(ContVar("α"))
    freeContVars(parse("μα.x")) shouldBe Set.empty
    freeContVars(parse("μα.[β] x")) shouldBe Set(ContVar("β"))
    freeContVars(parse("μα.[α] x")) shouldBe Set.empty
  }

  it should "handle free variables in thunk and force expressions" in {
    freeTermVars(parse("θx")) shouldBe Set(TermVar("x"))
    freeTermVars(parse("κx")) shouldBe Set(TermVar("x"))
    freeTermVars(parse("θ(λx.y)")) shouldBe Set(TermVar("y"))
    freeContVars(parse("θ([α] x)")) shouldBe Set(ContVar("α"))
  }

  "Substitution" should "substitute free variables" in {
    val expr = parse("x")
    val result = expr.subst(Map(TermVar("x") -> parse("y")))
    result shouldBe parse("y")
  }

  it should "not substitute bound variables" in {
    val expr = parse("λx.x")
    val result = expr.subst(Map(TermVar("x") -> parse("y")))
    shouldBeAlphaEq(result, parse("λx.x"))
  }

  it should "avoid variable capture" in {
    val expr = parse("λy.x")
    val result = expr.subst(Map(TermVar("x") -> parse("y")))
    result match {
      case Lam(param, body) =>
        param.name should not be "y"  // bound variable renamed
        body shouldBe parse("y")       // body should be the substituted free y
      case _ => fail("Expected lambda expression")
    }
  }

  it should "substitute in thunk and force expressions" in {
    val thunkExpr = parse("θx")
    val thunkResult = thunkExpr.subst(Map(TermVar("x") -> parse("y")))
    thunkResult shouldBe parse("θy")
    
    val forceExpr = parse("κx")
    val forceResult = forceExpr.subst(Map(TermVar("x") -> parse("y")))
    forceResult shouldBe parse("κy")
  }

  "Lazy evaluation vs Normalization" should "show the difference" in {
    // Church numeral arithmetic: succ 1 = 2
    val expr = parse("(λn.λf.λx.f (n f x)) (λf.λx.f x)")
    
    // Lazy evaluation stops at weak head normal form
    val lazy_result = expr.eval()
    lazy_result.pretty should include("λf")  // Should be a lambda but not fully reduced inside
    
    // Normalization continues reducing inside lambda bodies
    val normalized = lazy_result.normalize()
    val expected = parse("λf.λx.f (f x)")
    shouldBeAlphaEq(normalized, expected)
  }

  "Normalization" should "reduce inside lambda bodies" in {
    val expr = parse("λf.f ((λx.x) y)")
    val normalized = expr.normalize()
    normalized shouldBe parse("λf.f y")
  }

  it should "reduce inside application arguments" in {
    val expr = parse("f ((λx.x) y)")
    val normalized = expr.normalize()  
    normalized shouldBe parse("f y")
  }

  it should "handle nested reductions" in {
    val expr = parse("λf.λx.f ((λy.y) x)")
    val normalized = expr.normalize()
    normalized shouldBe parse("λf.λx.f x")
  }

  it should "work with mu expressions in reduction context" in {
    val expr = parse("μα.[α] x")  // This is in reduction context
    val normalized = expr.normalize()
    normalized shouldBe parse("x")  // This SHOULD reduce
  }

  it should "preserve mu expressions not in reduction context" in {
    val expr = parse("λf.f (μα.[β] x)")  // mu that CANNOT reduce (α ≠ β)
    val normalized = expr.normalize()
    normalized shouldBe parse("λf.f (μα.[β] x)")  // Should remain unchanged
  }

  it should "reduce structural congruence during normalization" in {
    val expr = parse("λf.[α] (μβ.[β] x)")  // [α] (μβ.[β] x) should reduce to [α] x
    val normalized = expr.normalize()
    normalized shouldBe parse("λf.[α] x")
  }

  it should "not change expressions already in normal form" in {
    val expr = parse("λf.λx.f x")
    val normalized = expr.normalize()
    normalized shouldBe expr
  }

  it should "normalize thunk and force expressions" in {
    val expr = parse("λf.f (κ(θ((λx.x) y)))")
    val normalized = expr.normalize()
    normalized shouldBe parse("λf.f y")
  }

  "Standard reduction rules" should "demonstrate all reduction types" in {
    // Beta: (λx.M) N → M[N/x]
    val beta = parse("(λx.x) y")
    beta.step shouldBe parse("y")

    // Mu: μα.[α] M → M  
    val mu = parse("μα.[α] x")
    mu.step shouldBe parse("x")

    // Structural: [α](μβ.c) → c[α/β]
    val structural = parse("[α] (μβ.[β] y)")
    structural.step shouldBe parse("[α] y")
    
    // Thunk/Force: κ(θ M) → M
    val thunkForce = parse("κ(θx)")
    thunkForce.step shouldBe parse("x")
  }

  "Classical logic features" should "demonstrate double negation elimination" in {
    val doubleNegElim = parse("λx.μα.x (λy.[α] y)")
    val doubleNegatedProof = parse("λf.f z")
    val application = Appl(doubleNegElim, doubleNegatedProof)
    val result = application.eval()
    result shouldBe parse("z")
  }

  it should "demonstrate Peirce's law with correct expectations" in {
    val peirce = parse("λf.μα.f (λx.[α] x)")
    val testFunction = parse("λg.μβ.[α] b")  // Note: α is FREE here
    val application = Appl(peirce, testFunction)
    val result = application.eval()
    
    // The result should be μα1.μβ.[α] b where:
    // - α1 is bound by outer μ (renamed to avoid capture)  
    // - β is bound by inner μ
    // - α is FREE (from the original testFunction)
    
    result match {
      case Mu(outerParam, Mu(innerParam, Cont(Var(ContVar(freeAlpha)), Var(TermVar("b"))))) =>
        // Check structure
        innerParam.name shouldBe "β"
        
        // The continuation variable should be the original free α, not the bound outer param
        freeAlpha should not be outerParam.name
        freeAlpha shouldBe "α"  // Original free variable
        
      case other => 
        fail(s"Expected μα1.μβ.[α] b structure, got: ${other.pretty}")
    }
  }

  "Complex expressions" should "handle function composition" in {
    val expr = parse("(λf.λg.λx.f (g x)) (λy.y) (λz.z)")
    val result = expr.eval().normalize()  // Need normalization for full reduction
    val expected = parse("λx.x")
    shouldBeAlphaEq(result, expected)
  }

  it should "handle mixed lambda-mu expressions" in {
    val expr = parse("(λx.μα.[α] x) (f y)")
    val result = expr.eval()
    result shouldBe parse("f y")
  }

  it should "handle mixed lambda-mu-thunk-force expressions" in {
    val expr = parse("(λx.κ(θx)) (f y)")
    val result = expr.eval()
    result shouldBe parse("f y")
  }

  "Pretty printing" should "handle parentheses correctly" in {
    parse("(λx.x) y").pretty shouldBe "(λx.x) y"
    parse("f (g h)").pretty shouldBe "f (g h)"
    parse("[α] (λx.x)").pretty shouldBe "[α] (λx.x)"
    parse("λx.(x y)").pretty shouldBe "λx.x y"
  }

  it should "print mu expressions correctly" in {
    parse("μα.[α] x").pretty shouldBe "μα.[α] x"
    parse("(μα.x) y").pretty shouldBe "(μα.x) y"
  }

  it should "print thunk and force expressions correctly" in {
    parse("θx").pretty shouldBe "θx"
    parse("κx").pretty shouldBe "κx"
    parse("θ(x y)").pretty shouldBe "θ(x y)"
    parse("κ(x y)").pretty shouldBe "κ(x y)"
  }

  "Evaluation termination" should "terminate on normalizing expressions" in {
    val expr = parse("(λx.x) y")
    val result = expr.eval()
    result shouldBe parse("y")
  }

  it should "handle non-terminating expressions gracefully" in {
    val omega = parse("(λx.x x) (λx.x x)")
    val result = omega.eval(maxSteps = 10)
    // Should stop after maxSteps and print warning
    result.pretty should include("λx.x x")  // Should still be some form of the expression
  }

  it should "demonstrate lazy evaluation prevents infinite loops in unused arguments" in {
    // (λx.y) omega should terminate in lazy evaluation
    val omega = parse("(λx.x x) (λx.x x)")
    val expr = Appl(parse("λx.y"), omega)
    val result = expr.eval(maxSteps = 5)  // Should terminate quickly
    result shouldBe parse("y")
  }

  it should "demonstrate thunks prevent infinite loops" in {
    // θ(omega) should not cause infinite loops
    val omega = parse("(λx.x x) (λx.x x)")
    val thunkedOmega = Thunk(omega)
    
    // Thunk should not evaluate its contents
    thunkedOmega.eval(maxSteps = 5) shouldBe thunkedOmega
    
    // Only forcing should potentially cause loops
    val forced = Force(thunkedOmega)
    val result = forced.step  // This gives us omega
    result shouldBe omega
  }

  "Recursive structures with thunks" should "demonstrate self-application without infinite loops" in {
    // F := λx.θ(x x) - creates a thunk of self-application
    val F = parse("λx.θ(x x)")
    val selfAppl = Appl(F, F)
    
    // F F should reduce to θ(F F) without infinite loops
    val result = selfAppl.step
    result shouldBe a[Thunk]
    
    // The thunk should contain F F
    result match {
      case Thunk(inner) => shouldBeAlphaEq(inner, selfAppl)
      case _ => fail("Expected thunk")
    }
  }

  it should "allow controlled unfolding via force" in {
    val F = parse("λx.θ(x x)")
    val selfAppl = Appl(F, F)
    val stepped = selfAppl.step  // θ(F F)
    
    // Forcing should give us F F again
    val forced = Force(stepped.asInstanceOf[Thunk])
    val forcedResult = forced.step
    shouldBeAlphaEq(forcedResult, selfAppl)
  }
}

