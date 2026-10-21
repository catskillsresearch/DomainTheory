# Proposition 4.2

I do not know at the time of writing whether this theorem on inverse limits of continuous lattices extends to sequences where, say, the $j_n$ are only retractions. Fortunately, sufficiently many projections exist to make this construction useful. Note that by reference to the product space construction of $D_{\infty}$, its lattice ordering is given simply by the relation:

$$x \sqsubseteq y \quad \text{iff} \quad x_n \sqsubseteq y_n \text{ for all } n.$$

**4.2 Proposition.** Let $\langle D_n, j_n \rangle_{n=0}^{\infty}$ and $D_{\infty}$ be as in 4.1. Then the maps $j_{\infty n} : D_{\infty} \to D_n$ are projections.

**Proof:** The projections $j_n : D_{n+1} \to D_n$, as we know, have their uniquely determined inverses $i_n : D_n \to D_{n+1}$. We can define $i_{n\infty} : D_n \to D_{\infty}$ by the equation:

$$i_{n\infty}(x) = \langle y_m \rangle_{m=0}^{\infty}$$

where

$$
y_m = \begin{cases}
j_m(y_{m+1}) & \text{if } m < n, 
x & \text{if } m = n, 
i_m(y_{m-1}) & \text{if } m > n.
\end{cases}
$$

The proof that $i_{n\infty}$ and $j_{\infty n}$ form a projection is now an easy computation. $\square$

**Lean 4**

- [ContinuousLattice/InverseLimits/proposition_4_2.lean](proposition_4_2.lean)
