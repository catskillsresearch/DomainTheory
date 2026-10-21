# Theorem 5.4

**THEOREM 5.4 (The product and sum theorem for algebraic lattices).** *Suppose that $a$ and $b$ are closure operations; then so are $a \boxtimes b$ and $a \boxplus b$. Analogues of the results in Theorems 4.4 and 4.5 carry over.*

Following the discussion in § 4, we can also show that the closure operations form a Cartesian closed category, which in some ways is better than the category of all retracts. What makes it better is the existence of a “universe”.

Every continuous operation generates a closure operation by just closing up the sets under the continuous function (as a set operation). We can institutionalize this thought by means of this definition:

$$(5.14) \quad \mathbf{V} = \lambda a \lambda x.\, \mathbf{Y}(\lambda y.\, x \cup a(y)).$$

Clearly $\mathbf{V}$ is LAMBDA-definable, continuous, etc. A more understandable characterization would define $\mathbf{V}(a)(x)$ by this equation:

$$(5.15) \quad \mathbf{V}(a)(x) = \bigcap \{ y \mid x \sqsubseteq y \text{ and } a(y) \sqsubseteq y \}.$$

These two definitions are easily seen to be equivalent. What is unexpected is the discovery (due in a different form to Peter Hancock and Per Martin-Löf) that $\mathbf{V}$ itself is a closure operation.

**Lean 4**

- [DataTypesAsLattices/Closures/theorem_5_4.lean](DomainTheory/DataTypesAsLattices/Closures/theorem_5_4.lean)
- [DataTypesAsLattices/Closures/theorem_5_4_plus.lean](DomainTheory/DataTypesAsLattices/Closures/theorem_5_4_plus.lean)
