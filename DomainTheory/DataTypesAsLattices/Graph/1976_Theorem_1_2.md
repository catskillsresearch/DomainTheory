# Theorem 1.2

**THEOREM 1.2** (The graph theorem). *Every continuous function is uniquely determined by its graph in the sense that:*

(i) $\mathbf{fun}(\mathbf{graph}(f)) = f.$

*Conversely, every set of integers determines a continuous function and we have:*

(ii) $u \subseteq \mathbf{graph}(\mathbf{fun}(u)),$

*where equality holds just in case $u$ satisfies:*

(iii) *whenever $(k, m) \in u$ and $e_k \subseteq e_n$, then $(n, m) \in u$.*

Besides functions of one variable we need to consider also functions of several variables. The official definition for one variable given above can be extended simply by saying $f(x, y, \dots)$ is continuous iff it is continuous in each of $x, y, \dots$. Those familiar with the product topology can prove that for our special positive topology on $\mathbf{P}\omega$ this is equivalent to being continuous on the product space (continuous in the variables jointly). Those interested only in elementary proofs can calculate out directly from the definition (with the aid of 1.1) that continuity behaves under combinations by substitution [as in: $f(g(x, y), h(y, x, y))$].

**Lean 4**

- [DataTypesAsLattices/Graph/theorem_1_2.lean](theorem_1_2.lean)
- [DataTypesAsLattices/Graph/theorem_1_2_i.lean](theorem_1_2_i.lean)
- [DataTypesAsLattices/Graph/theorem_1_2_ii.lean](theorem_1_2_ii.lean)
- [DataTypesAsLattices/Graph/theorem_1_2_iii.lean](theorem_1_2_iii.lean)
