# Corollary 3.4

The above theorem might possibly be generalized to $[X \to D]$ where $X$ is merely a $T_0$-space, but I was unable to see the argument. In any case we are mostly interested in the continuous lattices. Note as a consequence of our proof:

**3.4 Corollary.** For continuous lattices $D$ and $D'$, the evaluation map:

$$
\mathrm{eval} : [D \to D'] \times D \to D'
$$

is continuous.

**Proof:** Here $\mathrm{eval}(f, x) = f(x)$. With $f$ fixed, this is obviously continuous. With $x$ fixed, we proved the continuity above with our calculation of $\bigsqcup \mathcal{F}$ in view of 2.5. Hence applying 5.3 and 2.6, we conclude that $\mathrm{eval}$ is jointly continuous. $\square$

**Lean 4**

- [ContinuousLattice/FunctionSpaces/corollary_3_4.lean](corollary_3_4.lean)
- [ContinuousLattice/FunctionSpaces/corollary_3_4_eval_on_C.lean](corollary_3_4_eval_on_C.lean)
- [ContinuousLattice/FunctionSpaces/corollary_3_4_jointly_continuous.lean](corollary_3_4_jointly_continuous.lean)
- [ContinuousLattice/FunctionSpaces/corollary_3_4_preservesDirectedSup.lean](corollary_3_4_preservesDirectedSup.lean)
