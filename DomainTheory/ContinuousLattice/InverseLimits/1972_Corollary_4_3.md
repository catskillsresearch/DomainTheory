# Corollary 4.3

One should note also the recursion equation:

$$
i_{n\infty} = i_{(n+1)\infty} \circ i_n.
$$

These maps also make it possible to state this useful equation:

$$
x = \bigsqcup_{n=0}^{\infty} i_{n\infty}(x_n),
$$

where $x \in D_\infty$. It is easy to check that this is a monotone lub, and so we can say each $x \in D_\infty$ is the limit of its projections $x_n$. In fact, from what we know about projections, $x_n$ is the best possible approximation to $x$ in the space $D_n$.

**4.3 Corollary.** Let the spaces be as in 4.1 and 4.2. Let $D'$ be any complete lattice and suppose continuous functions $f_n : D_n \to D'$ are given so that $f_n = f_{n+1} \circ i_n$. Then we can define $f_\infty : D_\infty \to D'$ by the equation:

$$
f_\infty(x) = \bigsqcup_{n=0}^{\infty} f_n(x_n)
$$

for $x \in D_\infty$, and we have $f_n = f_\infty \circ i_{n\infty}$. $\square$

**Lean 4**

- [ContinuousLattice/InverseLimits/corollary_4_3.lean](corollary_4_3.lean)
