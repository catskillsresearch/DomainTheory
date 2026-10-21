# Proposition 3.7

**3.7 Proposition.** Suppose the two pairs of maps

$$i_n : D_n \to D'_n \quad \text{and} \quad j_n : D'_n \to D_n$$

for $n = 0,1$ make $D_n$ a retraction (projection) of $D'_n$. Then $[D_0 \rightarrow D_1]$ is also a retraction (projection) of $[D'_0 \rightarrow D'_1]$ by means of the pair of maps:

$$\vec{i}(f) = i_1 \circ f \circ j_0 \text{ , and}$$

$$\vec{j}(f') = j_1 \circ f' \circ i_0 \text{ ,}$$

where $f \in [D_0 \rightarrow D_1]$ and $f' \in [D'_0 \rightarrow D'_1]$. $\square$

**Lean 4**

- [ContinuousLattice/FunctionSpaces/proposition_3_7_projection.lean](DomainTheory/ContinuousLattice/FunctionSpaces/proposition_3_7_projection.lean)
- [ContinuousLattice/FunctionSpaces/proposition_3_7_retraction.lean](DomainTheory/ContinuousLattice/FunctionSpaces/proposition_3_7_retraction.lean)
