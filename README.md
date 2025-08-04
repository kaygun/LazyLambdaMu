# A Lazy Lambda-Mu Calculus Interpreter in Scala3

This is an interpreter for a lazy [Lambda-Mu calculus][1] implemented in Scala 3. I did use an LLM. Type "sbt run" to start the interpreter. You may load a library using the command `load filename` inside the interpreter. You may also define short-cuts via `let <name> = <lambda expression>`, and test alpha-equivalence via `<expression> == <expression>`. Type `:h` for help. 

[1]: https://en.wikipedia.org/wiki/Lambda-mu_calculus
