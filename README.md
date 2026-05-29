# Lazy $\lambda\mu$-Calculus Interpreter

A Scala 3 implementation of a lazy interpreter for Parigot's $\lambda\mu$-calculus. This project extends the standard $\lambda$-calculus with first-class continuations and explicit thunking/forcing operators to support infinite data structures and classical logic.

## Key Features

- **$\lambda\mu$-Calculus**: Supports $\mu$-abstraction for capturing continuations, allowing the implementation of control primitives like `call/cc`, exceptions, and proofs for classical logic (e.g., Peirce's Law).
- **Explicit Laziness**: Uses thunk ($\theta$) and force ($\kappa$) operators to manage evaluation, enabling the creation and manipulation of infinite streams.
- **Böhm Tree Semantics**: The interpreter evaluates terms toward their head normal form, effectively building (possibly infinite) Böhm trees.
- **Rich REPL**: Features include variable definitions (`let`), step-by-step reduction tracing, alpha-equivalence checking, and environment management.

## Syntax

The interpreter supports both mathematical symbols and ASCII alternatives:

| Construct | Syntax | ASCII | Description |
|-----------|--------|-------|-------------|
| **Lambda** | `λx. M` | `\x. M` | Function abstraction |
| **Mu** | `μα. M` | `#a. M` | Continuation abstraction |
| **Continuation** | `[α] M` | `[a] M` | Application to a continuation |
| **Thunk** | `θM` | `?M` | Suspend evaluation of $M$ |
| **Force** | `κM` | `!M` | Evaluate a suspended thunk |

## Getting Started

### Prerequisites
- [Scala 3](https://www.scala-lang.org/)
- [sbt](https://www.scala-sbt.org/)

### Running the REPL
```bash
sbt run
```

### Example Usage
Inside the REPL, you can define and explore infinite sequences:

```lambda
% Load the standard library
λμ> :load lib.lm

% Define an infinite stream of zeros
λμ> let zeros = (\x. pair zero (?(x x))) (\x. pair zero (?(x x)))

% Get the head of the stream
λμ> head zeros
λf.λx.x

% Trace the evaluation of the second element
λμ> :trace head (tail zeros)
```

## REPL Commands

- `let <name> = <expr>`: Define a global variable.
- `:load <file>`: Load definitions from a file.
- `:step <expr>`: Show a single step of $\beta/\mu$-reduction.
- `:trace <expr>`: Show the full reduction sequence.
- `<expr1> == <expr2>`: Check for alpha-equivalence.
- `:env`: View currently defined variables.
- `:help`: Show all available commands.

## Theoretical Background
For a detailed explanation of the implementation's relationship to Böhm Trees, anamorphisms, and self-similar structures, see [overview.md](overview.md).
