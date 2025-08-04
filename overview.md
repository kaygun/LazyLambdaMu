---
title: Böhm Trees and a Lazy $\lambda$-Calculus
---

I was very happy with [my earlier implementation][1] of [Parigot's $\lambda\mu$-calculus][2],
which by [Curry-Howard Isomorphism][3], is a model for [classical first order logic][9]. But I wanted
to implement [recursion][4] which requires a [lazy][5] version of what I did earlier. I decided
to use [anamorphisms][6] and self-similar trees.  [Böhm Trees][7] seemed to be the closest thing
to what I needed. So, I used them to implement a [lazy-$\lambda\mu$-calculus interpreter][8].

Below, you'll find the theoretical framework I used for my implementation.

[1]: https://github.com/kaygun/LambdaMu
[2]: https://en.wikipedia.org/wiki/Lambda-mu_calculus
[3]: https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence
[4]: https://en.wikipedia.org/wiki/Recursion_(computer_science)
[5]: https://en.wikipedia.org/wiki/Lazy_evaluation
[6]: https://en.wikipedia.org/wiki/Anamorphism
[7]: https://en.wikipedia.org/wiki/B%C3%B6hm_tree
[8]: https://github.com/kaygun/LazyLambdaMu
[9]: https://en.wikipedia.org/wiki/First-order_logic

##  $\lambda$-Expressions as Rooted Trees

The $\lambda$-calculus is a formal system defined by the following
grammar over a countable set of variables $\mathcal{V}$:
$$M ::= x \mid \lambda x. M \mid M\ N$$ where $x \in \mathcal{V}$,
$\lambda x. M$ is function abstraction, and $M\ N$ is application. Terms
are considered modulo $\alpha$-conversion. We write $\Lambda$ for the
set of all well-formed $\lambda$-terms. The semantics of computation is
determined by the notion of substitution $M[x := N]$ and the
$\beta$-reduction rule.

The $\beta$-reduction rule implements function application:
$$(\lambda x. M)\ N \to M[x := N]$$ This rule contracts redexes and
allows evaluation. The [Church-Rosser Theorem][10] states that
$\beta$-reduction is confluent:

[10]: https://en.wikipedia.org/wiki/Church%E2%80%93Rosser_theorem

::: theorem
**Theorem 1** (Church-Rosser). *If $M \twoheadrightarrow M_1$ and
$M \twoheadrightarrow M_2$, then there exists $N$ such that
$M_1 \twoheadrightarrow N$ and $M_2 \twoheadrightarrow N$.*
:::

This guarantees uniqueness of normal forms when they exist, and ensures
that evaluation strategy does not affect the outcome of normalization.

Each term $M\in\Lambda$ can be seen as a finite rooted tree. A variable
$x$ is a leaf. An abstraction $\lambda x. M$ becomes a unary node
labelled $\lambda x$ whose child is the tree for $M$. An application
$M\ N$ becomes a binary node with children corresponding to $M$ and $N$.
The root encodes the outermost constructor. Thus the syntax becomes a
free magma over constructors $x, \lambda, \text{app}$.

##  Recursion as Infinite Self-Similar Trees

Recursive functions can be viewed as infinite trees or as trees
containing cycles through delayed references. Consider the [fixed-point
combinator][11]: $$Y = \lambda f. (\lambda x. f(x\ x)) (\lambda x. f(x\ x))$$
This term unfolds recursively under $\beta$-reduction. For instance:
$$Y\ f \to f(Y\ f) \to f(f(Y\ f)) \to \dots$$ This yields an infinite
unfolding tree. Recursive functions thus give rise to infinite
self-similar structures which are not finitely representable without
sharing or delay.

[11]: https://en.wikipedia.org/wiki/Fixed-point_combinator

##  Böhm Trees

Given $M \in \Lambda$, the Böhm tree $BT(M)$ is a possibly infinite tree
that unfolds $M$'s weak head normal form. If
$$M \twoheadrightarrow_h \lambda x_1\dots x_n. x\ M_1\dots M_k$$ then
$$BT(M) = \lambda x_1\dots x_n. x\ BT(M_1)\dots BT(M_k)$$ If $M$ has no
weak head normal form, then $BT(M) = \bot$. Böhm trees expose the
computational structure of terms independent of evaluation strategies.
They are used in semantics to distinguish non-convertible terms and
describe observable behaviors.

##  Extending the $\lambda$-Calculus

To implement lazy evaluation, we introduce two new constructs:
$$M ::= x \mid \lambda x. M \mid M\ N \mid \theta M \mid \kappa M$$
where $\theta M$ suspends $M$, and $\kappa M$ forces the evaluation of a
thunk. We extend the operational semantics by:
$$\kappa(\theta M) \to M$$ This reduction allows delayed computations to
be evaluated only when needed. Unlike $\beta$-reduction, which
propagates evaluation through application, the presence of $\theta$
suspends it. Applications to recursive structures become possible
without immediate infinite unfolding. Furthermore, once the basic
reduction rule $\kappa(\theta M) \to M$ is introduced, we may observe
that both $\theta$ and $\kappa$ are idempotent up to operational
equivalence:
$$\theta(\theta M) \equiv \theta M, \quad \kappa(\kappa M) \equiv \kappa M$$
That is, suspending a computation already suspended has no further
effect, and forcing an already forced computation is operationally the
same. These equations ensure stability of the delayed evaluation
mechanism.

##  Recursion Revisited

In the presence of $\theta$ and $\kappa$, recursive definitions can be
directly encoded without relying on the Y combinator or named fixed
points. One may instead construct a recursive value using
self-application guarded by thunking. For instance, define:
$$F := \lambda x. \text{pair}\ 1\ (\theta(x\ x))$$ Let us write:
$$\text{Ones} := F F = (\lambda x. \text{pair}\ 1\ (\theta(x\ x)))\ (\lambda x. \text{pair}\ 1\ (\theta(x\ x)))$$
Applying a single $\beta$-reduction gives:
$$F\ F \to \text{pair}\ 1\ (\theta(F\ F))$$ This is a weak-head normal
form: the outermost $\text{pair}$ constructor is exposed, while the tail
is suspended. To force evaluation of the tail, we apply $\kappa$:
$$\kappa(\theta(F\ F)) \to F\ F \to \text{pair}\ 1\ (\theta(F\ F))$$
Each step thus yields a new $\text{pair}\ 1\ (\theta(\cdots))$ value.
Evaluation proceeds by recursively applying $\kappa$ to delayed tails:
$$\text{tail}_n := \underbrace{\kappa(\theta(\cdots\kappa(\theta}_{n\text{ times}}(\text{Ones})\cdots))$$
This results in an infinite stream of $1$'s, constructed lazily. Only
the demanded prefix is evaluated.

This formulation avoids fixed-point combinators and variable bindings,
relying solely on thunking and self-application to produce recursive
values. It gives a direct way to represent infinite computations with
explicit control over evaluation, naturally aligned with the semantics
of Böhm trees.

##  Functional Streams and Thunked Recursion

The use of $\theta$ in self-referential definitions becomes more subtle
when recursion depends on the result of previous computation. Consider a
function for mapping a function over an infinite list:
$$\text{map} := \lambda f. \lambda x. \text{pair}\ (f (\text{head}\ x))\ (\theta(\text{map}\ f\ (\text{tail}\ x)))$$
This definition is inherently recursive. To encode it anonymously using
thunked self-application, we write:
$$F := \lambda x. \text{pair}\ (f(\text{head}(\kappa x)))\ (\theta(F\ (\text{tail}(\kappa x))))$$
and define the stream as $F\ (\theta F)$. This ensures the recursive
call is delayed and will be evaluated only upon forcing.

Attempting instead to use $F\ F$ directly would result in immediate
recursion: the term $x\ x$ appears in a non-delayed position and is
evaluated eagerly, leading to nontermination. In contrast, the constant
stream $\text{Ones} = F\ F$ works because the self-reference occurs only
inside a $\theta$ and is thus suspended.

This example demonstrates that when recursive references appear in
non-delayed contexts (e.g., as arguments to $f$, $\text{head}$, or
$\text{tail}$), the self-reference must be wrapped in $\theta$. The
thunk ensures that $\kappa$ mediates recursive forcing, providing
fine-grained control over evaluation.

As a further example, consider the lazy infinite sequence of Church
numerals starting at zero:
$$\text{Zero} := \lambda f. \lambda x. x \quad \text{Succ} := \lambda n. \lambda f. \lambda x. f (n f x)$$
Define:
$$F := \lambda x. \text{pair}\ \text{Zero}\ (\theta(\text{map}\ \text{Succ}\ (\kappa x)))$$
Then the stream of Church numerals is given by $F\ (\theta F)$. Each
forced tail applies the successor function to the head of the stream
recursively, yielding:
$$\text{pair}\ \text{Zero}\ (\theta(\text{pair}\ (\text{Succ}\ \text{Zero})\ (\theta(\cdots))))$$
This gives a lazy list of Church numerals $0, 1, 2, \dots$ defined by
primitive recursion over $\kappa x$.

## References

**$\lambda$-Calculus Foundations**

- **Church, Alonzo (1936).** *An unsolvable problem of elementary number theory.* *American Journal of Mathematics*, **58**(2), 345–363.  
- **Curry, Haskell B. (1934).** *Functionality in combinatory logic.* *Proceedings of the National Academy of Sciences*, **20**(11), 584–590.

***Böhm Trees and Denotational Semantics***

- **Barendregt, Henk P. (1984).** *The Lambda Calculus: Its Syntax and Semantics.* 2nd ed., North-Holland.  
- **Lévy, Jean-Jacques (1975).** *An algebraic interpretation of the λβK-calculus and a labelled λ-calculus.* In *LNCS 37: Lambda-Calculus and Computer Science Theory*, pp. 147–165.  
- **Wadsworth, Christopher P. (1976).** *The relation between computational and denotational properties for Scott’s D∞-models of the lambda-calculus.* *SIAM Journal on Computing*, **5**(3), 488–521.  
- **Plotkin, Gordon D. (1975).** *Call-by-name, Call-by-value and the λ-calculus.* *Theoretical Computer Science*, **1**(2), 125–159.

**$\lambda\mu$-Calculus and Classical Control**

- **Parigot, Michel (1992).** *λμ-Calculus: An Algorithmic Interpretation of Classical Natural Deduction.* In *LPAR ’92*, *LNCS 624*, pp. 190–201.  
- **Curien, Pierre-Louis & Herbelin, Hugo (2000).** *The Duality of Computation.* In *ICFP 2000*.  
- **Laird, James (2020).** *A Curry-style Semantics of Interaction: From Untyped to Second-Order Lazy λμ-Calculus.* In *FoSSaCS 2020*, *LNCS 12077*, pp. 422–441.

**Lazy Evaluation and Call-by-Need**

- **Wadsworth, Christopher P. (1971).** *Semantics and Pragmatics of the Lambda-Calculus.* D.Phil. Thesis, Oxford University.  
- **Henderson, Peter & Morris Jr., James H. (1976).** *A Lazy Evaluator.* In *Proceedings of the 3rd ACM SIGACT-SIGPLAN Symposium on Principles of Programming Languages (POPL '76)*, pp. 95–103.  
- **Friedman, Daniel P. & Wise, David S. (1976).** *Cons should not evaluate its arguments.* In *ICALP '76*, Edinburgh University Press, pp. 257–284.  
- **Launchbury, John (1993).** *A Natural Semantics for Lazy Evaluation.* In *POPL '93*, pp. 144–154.  
- **Ariola, Zena M. et al. (1995).** *The Call-by-Need Lambda Calculus.* In *POPL '95*, pp. 233–246.

