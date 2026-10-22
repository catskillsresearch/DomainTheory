# Proposition 5.4

The purpose of giving the above proof was to illustrate the use of the least fixed-point operator in proofs. We have such true principles as:

$$! x . \tau(x) = \tau(! x . \tau(x));$$

and

$$\tau(y) \sqsubseteq y \text{ implies } ! x . \tau(x) \sqsubseteq y,$$

provided, of course, that $x$ is not free in $\tau$. These, together with the monotonicity of all the functions, were just the methods used in the above proof. Here is another example.

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
As this holds for all $x$, then $f \sqsubseteq g_0$ follows. So the equation is true. $\square$

The last proof is instructive as it uses equations and inclusions between functions. In particular we have just made use of the principle:

> if $\tau \sqsubseteq \sigma$ holds for all values of $x$,  
> then $\lambda x . \tau \sqsubseteq \lambda x . \sigma$ holds.

This is another form of Theorem 3.13(i).

**TABLE 5.5.** In the displayed table we give a summary of uses of the $\lambda$-notation to define various combinators. We have mentioned some of these equations before, and there are some combinators here we have not mentioned before — their meanings, however, should be clear.

$$
\begin{aligned}
P_0 &= \lambda x, y . x \\
P_1 &= \lambda x, y . y \\
\mathrm{pair} &= \lambda x \lambda y . \langle x, y \rangle \\
\mathrm{n\text{-}tuple} &= \lambda x_0 \lambda x_1 \ldots \lambda x_{n-1} . \langle x_0, x_1, \ldots, x_{n-1} \rangle \\
\mathrm{diag} &= \lambda x . \langle x, x \rangle \\
\mathrm{funpair} &= \lambda f \lambda g \lambda x . \langle f(x), g(x) \rangle \\
\mathrm{proj}_i^n &= \lambda x_0, x_1, \ldots, x_{n-1} . x_i \\
\mathrm{inv}_{i,j}^n &= \lambda x_0, \ldots, x_i, \ldots, x_j, \ldots, x_{n-1} . \langle x_0, \ldots, x_j, \ldots, x_i, \ldots, x_{n-1} \rangle
\end{aligned}
$$

$$
\begin{aligned}
\mathrm{eval} &= \lambda f, x . f(x) \\
\mathrm{curry} &= \lambda g \lambda x \lambda y . g(x, y) \\
\mathrm{comp} &= \lambda g, f \lambda x . g(f(x)) \\
\mathrm{const} &= \lambda k \lambda x . k \\
\mathrm{fix} &= \lambda f ! x . f(x)
\end{aligned}
$$

**A TABLE OF COMBINATORS**
It is important to note that since we have not typed the variables, these equations are ambiguous: they only become precise when the types are specified. It follows, therefore, that what we find in the table are *schemes* for combinators; there are actually infinitely many distinct combinators corresponding to any one equation depending on how the variables have types chosen for them. Clearly it is better to imagine this variety of combinators than it is to try to notate them with type superscripts.

One interest of combinators is that it is often possible to write expressions without variables — if enough combinators are used. This is sometimes useful, but it can become clumsy. On the other hand, if the same combination occurs over and over, it is sometimes useful to give it a name. This is what we do with, say, *composition* where

$$
\mathrm{comp}\ (g, f) = g \circ f.
$$

On the one side we have the prefix notation, and on the other, the more common infix notation. With either notation the variable seen in $\lambda x.\ g(f(x))$ has been got rid of. The choice between equivalent notations ought to be based on a desire for readability. $\square$

**Lean 4**

- [NeighbourhoodSystems/TypedLambdaCalculus/Proposition54/pfix.lean](pfix.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Proposition54/pfix_apply.lean](pfix_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Proposition54/recOp.lean](recOp.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Proposition54/recOp_apply.lean](recOp_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Proposition54/sectionu2082_apply.lean](sectionu2082_apply.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Proposition54/pfix_isFixed.lean](pfix_isFixed.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Proposition54/pfix_eq_fixElement_recOp.lean](pfix_eq_fixElement_recOp.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Proposition54.lean](../Proposition54.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Proposition54/section₂.lean](section₂.lean)
- [NeighbourhoodSystems/TypedLambdaCalculus/Proposition54/Basic.lean](Basic.lean)
