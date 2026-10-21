# Proposition 3.8

Returning now to $\bar{f}$ we can prove:

**3.8 Proposition.** If $D$ is a continuous lattice and $e : X \rightarrow Y$ a subspace embedding, then for each $f : X \rightarrow D$, the function $\bar{f} : Y \rightarrow D$ given by the formula

$$\bar{f}(y) = \bigsqcup  \sqcap  f(x) : e(x) \in U  : y \in U ,$$

where $U$ ranges over open subsets of $Y$ and $x$ over $X$, is the maximal extension of $f$ to a function in the partially ordered set $[Y \rightarrow D]$.

**Proof:** We are saying that $\bar{f}$ is the maximal solution to the equation

$$f = \bar{f} \circ e.$$

We already know it is a solution, so let $f'$ be any other. We have

$$
\begin{aligned}
f'(y) &= \bigsqcup  \sqcap  f'(z) : z \in U  : y \in U  
&\sqsubseteq \bigsqcup  \sqcap  f'(z) : z \in e(X) \cap U  : y \in U  
&= \bigsqcup  \sqcap  f'(e(x)) : e(x) \in U  : y \in U  
&= \bigsqcup  \sqcap  f(x) : e(x) \in U  : y \in U  
&= \bar{f}(y),
\end{aligned}
$$

which establishes that $f' \sqsubseteq \bar{f}$. $\square$

**Lean 4**

- [ContinuousLattice/Constructions/proposition_3_8.lean](proposition_3_8.lean)
