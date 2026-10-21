# Proposition 3.5

This result gives only one example of the masses of continuous functions that are available on continuous lattices. As another fundamental example we have:

**3.5 Proposition.** For continuous lattices $D$, $D'$, and $D''$, the map of functional abstraction:

$$
\mathrm{lambda} : [[D \times D'] \to D''] \to [D \to [D' \to D'']]
$$

is continuous.

**Proof:** Here lambda is defined by:

$$
\mathrm{lambda}(f)(x)(y) = f(x,y)
$$

where $f \in [[D \times D'] \to D'']$ and $x \in D$ and $y \in D'$. What is particularly interesting here is that by virtue of 3.3 we are making use of $[D \to [D' \to D'']]$ as a continuous lattice. The principle being stated here can be formulated more broadly in this way:

> If an expression $\mathcal{E}(x, y, z, \dots)$ is continuous in all its variables $x, y, z, \dots$ with values in $D'$ as $x$ ranges in $D$, then the expression
>
> $$\lambda x : D . \mathcal{E}(x, y, z, \dots)$$
>
> with values in $[D \to D']$ is continuous in the remaining variables $y, z, \dots$ .

The $\lambda$-notation is a notation for functions, where in the above the variable after the $\lambda$ is the *argument* and the expression after the $.$ is the *value* (as a function of the argument). Thus we could write:

$$
\mathrm{lambda} = \lambda f : [[D \times D'] \to D''] . \lambda x : D . \lambda y : D' . f(x,y),
$$

and, because $f(x,y)$ is continuous in $f$, $x$, and $y$, our conclusion follows. But often it is more readable not to write equations between functions but rather equations between values for definitional purposes.

The proof of the principle is easy. For let the variable $y$, say range over $D''$ and let $S \subseteq D''$ be a directed subset. Then

$$
\begin{aligned}
\lambda x : D . \mathcal{E}(x, \bigsqcup S, z, \dots) &= \lambda x : D . \bigsqcup  \mathcal{E}(x, y, z, \dots) : y \in S  
&= \bigsqcup  \lambda x : D . \mathcal{E}(x, y, z, \dots) : y \in S ,
\end{aligned}
$$

because the lubs of functions are computed pointwise. $\square$

**Lean 4**

- [ContinuousLattice/FunctionSpaces/proposition_3_5.lean](proposition_3_5.lean)
- [ContinuousLattice/FunctionSpaces/proposition_3_5_preservesDirectedSup.lean](proposition_3_5_preservesDirectedSup.lean)
