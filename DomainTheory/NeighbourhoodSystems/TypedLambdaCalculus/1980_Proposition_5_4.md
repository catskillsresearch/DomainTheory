# Proposition 5.4

## Human-English

**PROPOSITION 5.4.** Let $x$, $y$, and $\tau(x, y)$ be of the same type $D$ and let $g$ be of type $(D \to D)$, then the equation

$$\lambda x . ! y . \tau(x, y) = ! g . \lambda x . \tau(x, g(x))$$

is true.

*Proof :* Let $f$ be the function on the left-hand side. We can write

$$f(x) = ! y . \tau(x, y) = \tau(x, f(x)).$$

Therefore

$$f = \lambda x . \tau(x, f(x)),$$

and it follows that

$$g_0 = ! g . \lambda x . \tau(x, g(x)) \sqsubseteq f.$$

Then we have at once, by definition of $g_0$,

$$g_0(x) = \tau(x, g_0(x)),$$

for any given $x$. But by definition of $f$ we find

$$f(x) = ! y . \tau(x, y) \sqsubseteq g_0(x).$$

<!-- page 83 -->

As this holds for all $x$, then $f \sqsubseteq g_0$ follows. So the equation is true. $\square$

The last proof is instructive as it uses equations and inclusions between functions. In particular we have just made use of the principle:

> if $\tau \sqsubseteq \sigma$ holds for all values of $x$,  
> then $\lambda x . \tau \sqsubseteq \lambda x . \sigma$ holds.

This is another form of Theorem 3.13(i).

## AI: Human-English to AI-Lean

**[Proposition_5_4.lean](Proposition_5_4.lean)**

@import "Proposition_5_4.lean"
