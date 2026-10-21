# Theorem 1.5

**THEOREM 1.5** (The extension theorem). *Let $X$ and $Y$ be arbitrary topological spaces where $X \subseteq Y$ as a subspace. Then every continuous function $f : X \to \mathbf{P}\omega$ can be extended to a continuous function $\bar{f} : Y \to \mathbf{P}\omega$ defined by the equation:*

$$\bar{f}(y) = \bigcup \{ \bigcap \{ f(x) \mid x \in X \cap U \} \mid y \in U \},$$

*where $y \in Y$, and $U$ ranges over the open subsets of $Y$.*

**Lean 4**

- [DataTypesAsLattices/Embedding/theorem_1_5.lean](DomainTheory/DataTypesAsLattices/Embedding/theorem_1_5.lean)
- [DataTypesAsLattices/Embedding/theorem_1_5_extends.lean](DomainTheory/DataTypesAsLattices/Embedding/theorem_1_5_extends.lean)
