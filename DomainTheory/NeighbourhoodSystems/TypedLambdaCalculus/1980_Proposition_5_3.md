# Proposition 5.3

## Human-English

**PROPOSITION 5.3.** The least fixed point of $\lambda x, y.\ \langle \tau(x, y), \sigma(x, y) \rangle$ is the pair with coordinates

$! x.\ \tau(x,\ ! y.\ \sigma(x, y))$ and

$! y.\ \sigma(! x.\ \tau(x, y), y)$.

**Proof:** (We are assuming that $x$ and $y$ are not free in $\tau$ and $\sigma$.) The purpose of the fixed-point search is to find the least solution of the pair of equations $x = \tau(x, y)$ and $y = \sigma(x, y)$. In other words, we are generalizing the fixed-point equation from one to two variables—and, of course, we could go much further to any number of variables. To this end, let

$y_* = ! y.\ \sigma(! x.\ \tau(x, y), y)$, and

$x_* = ! x.\ \tau(x, y_*)$.

Then

$x_* = \tau(x_*, y_*)$,

and

$y_* = \sigma(! x.\ \tau(x, y_*), y_*)$

$= \sigma(x_*, y_*)$.

This proves that $\langle x_*, y_* \rangle$ is one fixed-point pair.

Suppose, then, that $\langle x_0, y_0 \rangle$ is the least solution. (Why does a least solution have to exist? Hint: Consider a suitable mapping of type $D_0 \times D_1 \to D_0 \times D_1$, where $D_0$ is the type of $x$ and $D_1$ the type of $y$.) Then we know $x_0 = \tau(x_0, y_0)$ and $y_0 = \sigma(x_0, y_0)$, and also $x_0 \sqsubseteq x_*$ and $y_0 \sqsubseteq y_*$. But from

$\tau(x_0, y_0) \sqsubseteq x_0$,

it follows that

$! x.\ \tau(x, y_0) \sqsubseteq x_0$.

<!-- page 82 -->

Consequently,

$$\sigma(! x . \tau(x, y_0), y_0) \sqsubseteq \sigma(x_0, y_0) \sqsubseteq y_0.$$

By the fixed-point definition of $y_*$, we have $y_* \sqsubseteq y_0$, so $y_* = y_0$; whence,

$$x_* = ! x . \tau(x, y_*) = ! x . \tau(x, y_0) \sqsubseteq x_0.$$

So also $x_* = x_0$. $\square$ We have the right formula for $y_0$, and a similar argument gives $x_0$.

The purpose of giving the above proof was to illustrate the use of the least fixed-point operator in proofs. We have such true principles as:

$$! x . \tau(x) = \tau(! x . \tau(x));$$

and

$$\tau(y) \sqsubseteq y \text{ implies } ! x . \tau(x) \sqsubseteq y,$$

provided, of course, that $x$ is not free in $\tau$. These, together with the monotonicity of all the functions, were just the methods used in the above proof. Here is another example.

## AI: Human-English to AI-Lean

**[Proposition_5_3.lean](Proposition_5_3.lean)**

@import "Proposition_5_3.lean"
