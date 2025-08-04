import scala.io.StdIn.readLine
import scala.collection.mutable
import java.io.{PrintWriter, File}
import scala.io.Source
import scala.util.{Try, Success, Failure}

object REPL extends App:
  private val environment: mutable.Map[TermVar, Term] = mutable.Map.empty

  private def withFile[T](filename: String, operation: String)(action: => T): Unit =
    Try(action) match
      case Success(_) => println(s"$operation successful: $filename")
      case Failure(e) => println(s"Error during $operation of $filename: ${e.getMessage}")

  private def resolve(expr: Term, bound: Set[Name] = Set.empty, depth: Int = 0): Term = {
    if (depth > 100) return expr
    
    expr match
      case Var(x) =>
        if bound.contains(x) then Var(x)
        else x match
          case tv: TermVar => environment.getOrElse(tv, Var(tv))
          case cv: ContVar => Var(cv)
      case Lam(param, body) => Lam(param, resolve(body, bound + param, depth + 1))
      case Mu(param, body) => Mu(param, resolve(body, bound + param, depth + 1))
      case Appl(head, arg) => Appl(resolve(head, bound, depth + 1), resolve(arg, bound, depth + 1))
      case Cont(head, arg) => Cont(resolve(head, bound, depth + 1), resolve(arg, bound, depth + 1))
      case Thunk(term) => Thunk(resolve(term, bound, depth + 1))
      case Force(term) => Force(resolve(term, bound, depth + 1))
  }

  private def saveEnv(filename: String): Unit = withFile(filename, "Environment save") {
    val out = new PrintWriter(File(filename))
    try environment.foreach { case (k, v) => out.println(s"let ${k.name} = ${v.pretty}") }
    finally out.close()
  }

  private def loadEnv(filename: String): Unit = withFile(filename, "Environment load") {
    for line <- Source.fromFile(filename).getLines do
      if line.trim.startsWith("let ") then
        parseLet(line.trim.drop(4)) match
          case Some((name, expr)) => environment(TermVar(name)) = resolve(expr)
          case None => println(s"Invalid line: $line")
  }

  private def parseLet(letContent: String): Option[(String, Term)] =
    letContent.split("=", 2).map(_.trim) match
      case Array(name, exprStr) if name.nonEmpty && exprStr.nonEmpty =>
        LambdaParser.parseExpr(exprStr).toOption.map(name -> _)
      case _ => None

  private def evaluateExpression(expr: Term): Term =
    val resolved = resolve(expr)
    val evaluated = resolved.eval()
    evaluated.normalize()

  private def showStep(exprStr: String): Unit =
    LambdaParser.parseExpr(exprStr) match
      case Right(expr) =>
        val resolved = resolve(expr)
        val stepped = resolved.step
        if stepped.alphaEq(resolved) then
          println(s"${resolved.pretty} (already in normal form)")
        else
          println(s"${resolved.pretty} → ${stepped.pretty}")
      case Left(err) => println(err)

  private def showTrace(exprStr: String): Unit =
    LambdaParser.parseExpr(exprStr) match
      case Right(expr) =>
        val resolved = resolve(expr)
        traceReduction(resolved)
      case Left(err) => println(err)

  private def traceReduction(expr: Term, maxSteps: Int = 400): Unit =
    var current = expr
    var stepCount = 0
    var continuing = true
    
    println(s"[$stepCount]: ${current.pretty}")
    
    // First, show the step-by-step lazy evaluation
    while stepCount < maxSteps && continuing do
      val next = current.step
      stepCount += 1
      if next.alphaEq(current) then
        println(s"[$stepCount]: (lazy evaluation complete)")
        continuing = false
      else
        current = next
        println(s"[$stepCount]: ${current.pretty}")
    
    // Then show the final normalized result
    val normalized = current.normalize()
    if !normalized.alphaEq(current) then
      println(s"[normalized]: ${normalized.pretty}")
    else
      println("(already fully normalized)")
    
    if stepCount >= maxSteps then
      println(s"Stopped after $maxSteps steps")

  private def checkAlphaEquivalence(line: String): Unit =
    val parts = line.split("==", 2)
    if parts.length != 2 then
      println("Usage: <expr1> == <expr2>")
    else
      val expr1Str = parts(0).trim
      val expr2Str = parts(1).trim
      
      (LambdaParser.parseExpr(expr1Str), LambdaParser.parseExpr(expr2Str)) match
        case (Right(expr1), Right(expr2)) =>
          val resolved1 = resolve(expr1)
          val resolved2 = resolve(expr2)
          val areAlphaEq = resolved1.alphaEq(resolved2)
          
          println(s"${resolved1.pretty} == ${resolved2.pretty}")
          println(areAlphaEq)
            
        case (Left(err1), _) => println(s"Parse error in first expression: $err1")
        case (_, Left(err2)) => println(s"Parse error in second expression: $err2")

  private object Commands:
    def help(): Unit =
      println("""Commands:
        |  let <n> = <expr>     - Define a variable
        |  :env                 - Show environment
        |  :clear               - Clear environment
        |  :save <file>         - Save environment to file
        |  :load <file>         - Load environment from file
        |  :step <expr>         - Show single step reduction
        |  :trace <expr>        - Show step-by-step evaluation
        |  :help, :h            - Show this help
        |  :quit, :q            - Exit REPL
        |  <expr>               - Evaluate expression (with normalization)
        |  
        |Thunk/Force operators:
        |  θ<expr> or ?<expr>   - Thunk (suspend evaluation)
        |  κ<expr> or !<expr>   - Force (evaluate thunks)
        |  
        |Note: Evaluation uses lazy evaluation + normalization for full reduction.""".stripMargin)

    def showEnv(): Unit =
      if environment.isEmpty then println("Empty environment")
      else environment.toSeq.sortBy(_._1.name).foreach((k, v) => println(s"${k.name} = ${v.pretty}"))

    def clearEnv(): Unit =
      environment.clear()
      println("Environment cleared")

    def defineLet(letContent: String): Unit =
      parseLet(letContent) match
        case Some((name, expr)) =>
          val resolved = resolve(expr)
          environment(TermVar(name)) = resolved
          println(s"$name = ${resolved.pretty}")
        case None => println("Usage: let <n> = <expr>")

  private def processCommand(input: String): Boolean = input.trim match
    case ":q" | ":quit" => 
      println("Goodbye!")
      false
      
    case ":help" | ":h" => Commands.help(); true
    case ":env" => Commands.showEnv(); true
    case ":clear" => Commands.clearEnv(); true
    
    case line if line.startsWith(":step ") =>
      showStep(line.stripPrefix(":step ").trim)
      true
      
    case line if line.startsWith(":trace ") =>
      showTrace(line.stripPrefix(":trace ").trim)
      true
      
    case line if line.startsWith(":save ") =>
      saveEnv(line.stripPrefix(":save ").trim)
      true
      
    case line if line.startsWith(":load ") =>
      loadEnv(line.stripPrefix(":load ").trim)
      true
      
    case line if line.contains("==") =>
      checkAlphaEquivalence(line)
      true
      
    case line if line.startsWith("let ") =>
      Commands.defineLet(line.drop(4))
      true
      
    case line if line.nonEmpty =>
      LambdaParser.parseExpr(line) match
        case Right(expr) => 
          val result = evaluateExpression(expr)
          println(result.pretty)
        case Left(err) => println(err)
      true
      
    case _ => true

  println("λμ-calculus REPL with Thunk (θ/?) and Force (κ/!) operators")
  println("Lazy evaluation with normalization for complete reduction")
  println("Type :help for commands, :q to quit")

  Iterator.continually(readLine("λμ> "))
    .takeWhile(_ != null)
    .map(processCommand)
    .takeWhile(identity)
    .foreach(_ => ())
