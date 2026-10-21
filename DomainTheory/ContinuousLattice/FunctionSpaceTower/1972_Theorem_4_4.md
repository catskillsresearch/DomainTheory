# Theorem 4.4

The import of this last result is that within the category of complete lattices, the space $D_\infty$ is not only the inverse limit of the $D_n$, but it is also the *direct* limit. (One system of spaces here uses the $j_n$ as connecting maps, the other the $i_n$.) This is the algebraic result that lies at the heart of our main result about inverse limits of function spaces.

Turning to function spaces, let $D = D_0$ be a given continuous lattice. As we have seen in 3.13, there are many ways of making $D_0$ a projection of $D_1 = [D_0 \to D_0]$. Choose one such given by a pair $i_0, j_0$. Define recursively:

$$
D_{n+1} = [D_n \to D_n]
$$

and introduce the pairs $i_{n+1}, j_{n+1}$ making $D_{n+1}$ a projection of $D_{n+2}$ by the method of 3.7. Specifically we shall have for $x \in D_{n+1}$ and $x' \in D_{n+2}$:

$$
i_{n+1}(x) = i_n \circ x \circ j_n,
$$

$$
j_{n+1}(x') = j_n \circ x' \circ i_n.
$$

Since these spaces are more than continuous lattices being function spaces, it is interesting to note that the maps $i_n$ preserve function value as an algebraic operation as follows:

$$
i_n(f(x)) = i_{n+1}(f)(i_n(x)),
$$

where $x \in D_n$ and $f \in D_{n+1}$. Thus in passing to the limit space $D_\infty$ something of functional application must also be preserved. The precise result shows that indeed $D_\infty$ becomes its own function space.

**4.4 Theorem.** *The inverse limit $D_\infty$ of the recursively defined sequence $\langle D_n, j_n \rangle_{n=0}^{\infty}$ of function spaces is not only a continuous lattice, but it is also homeomorphic to its own function space $[D_\infty \to D_\infty]$.*

**Proof:** We can write down directly the pair of maps $i_\infty, j_\infty$ that provide the homeomorphism:

$$
i_\infty(x) = \bigsqcup_{n=0}^{\infty} (i_{n\infty} \circ x_{n+1} \circ j_{\infty n}),
$$

$$
j_\infty(f) = \bigsqcup_{n=0}^{\infty} i_{(n+1)\infty}(j_{\infty n} \circ f \circ i_{n\infty}).
$$

Note that these formulae are simply generalizations at the limit for the formulae we used to define $i_n, j_n$ in the first place. Thus it is not surprising that they would provide a projection of $[D_\infty \to D_\infty]$ upon $D_\infty$. Indeed we can compute out $j_\infty(i_\infty(x))$, noting that all the lubs are monotone and that a double monotone limit can always be replaced by a single one in view of the continuity of the operations involved, obtaining

$$
\begin{aligned}
j_\infty(i_\infty(x)) &= \bigsqcup_{n=0}^{\infty} i_{(n+1)\infty}(j_{\infty n} \circ i_{n\infty} \circ x_{n+1} \circ j_{\infty n} \circ i_{n\infty}) 
&= \bigsqcup_{n=0}^{\infty} i_{(n+1)\infty}(x_{n+1}) 
&= x.
\end{aligned}
$$

In the converse order the calculation is only a bit more complicated. The idea is that since all the functions $f$ are continuous and since the elements $x$ are the limits of their approximations, then each $f$ is actually completely determined by its

In the converse order the calculation is only a bit more complicated. The idea is that since all the functions $f$ are continuous and since the elements $x$ are the limits of their approximations, then each $f$ is actually completely determined by its sequence of restrictions $j_{\infty n} \circ f \circ i_{n\infty} \in D_{n+1}$. This simple idea can be made more precise with the aid of a lemma about $D_\infty$, which allows us in certain cases to recognize projections from limits.

**Proof of 4.4 concluded:** The lemma applies at once to our calculation, for we find:

$$
\begin{aligned}
i_\infty(j_\infty(f)) &= \bigsqcup_{n=0}^{\infty} (i_{n\infty} \circ j_{\infty n} \circ f \circ i_{n\infty} \circ j_{\infty n}) 
&= \bigsqcup_{n=0}^{\infty} (i_{n\infty} \circ j_{\infty n}) \circ f \circ \bigsqcup_{n=0}^{\infty} (i_{n\infty} \circ j_{\infty n}).
\end{aligned}
$$

Here we have just applied the continuity of $f$ to be able to confine the lub on the right. But now by the remark following 4.2, we note the functional equation:

$$\mathrm{id} = \bigsqcup_{n=0}^{\infty} (i_{n\infty} \circ j_{\infty n}),$$

and the proof that $i_\infty$ and $j_\infty$ are inverse to one another is complete. $\square$

**Lean 4**

- [ContinuousLattice/FunctionSpaceTower/theorem_4_4.lean](theorem_4_4.lean)
- [ContinuousLattice/FunctionSpaceTower/theorem_4_4_inverses.lean](theorem_4_4_inverses.lean)
- [ContinuousLattice/FunctionSpaceTower/theorem_4_4_orderIso.lean](theorem_4_4_orderIso.lean)
- [ContinuousLattice/FunctionSpaceTower/theorem_4_4_scottTopology_homeomorph.lean](theorem_4_4_scottTopology_homeomorph.lean)
- [ContinuousLattice/FunctionSpaceTower/theorem_4_4_sourceTopology_homeomorph.lean](theorem_4_4_sourceTopology_homeomorph.lean)
