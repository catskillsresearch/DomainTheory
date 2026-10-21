# Theorem 1.1

**THEOREM 1.1** (The characterization theorem). A function $f : \mathbf{P}\omega \to \mathbf{P}\omega$ is *continuous* iff for all $x \in \mathbf{P}\omega$ and all $e_m$ we have:

$$e_m \subseteq f(x) \quad \text{iff} \quad \exists e_n \subseteq x.\; e_m \subseteq f(e_n).$$

Note that open sets and continuous functions have a *monotonicity property*:

*whenever* $x \subseteq y$ *and* $x \in U$, *then* $y \in U$; *and*

*whenever* $x \subseteq y$, *then* $f(x) \subseteq f(y)$.

This gives a precise expression to the “positive” character of our topology. However, note too that openness and continuity mean rather more than just monotonicity. In particular, a continuous function is completely determined by the pairs of integers $n, m$ such that $m \in f(e_n)$, as can be seen from the definition. (Hence, there are only a continuum number of continuous functions, but more than a continuum number of monotonic functions.) This brings us to the definition of the *graph* of a continuous function.

To formulate the definition, we introduce a standard enumeration $(n, m)$ of all pairs of integers. Specifically we set

$$(n, m) = \tfrac{1}{2}(n + m)(n + m + 1) + m.$$

This is the enumeration along the “little diagonals” going from left to right, and it produces the ordering:

$$(0, 0), (1, 0), (0, 1), (2, 0), (1, 1), (0, 2), (3, 0), (2, 1), \dots.$$

Note that $n \leq (n, m)$ and $m \leq (n, m)$ with equality possible only in the cases of $(0, 0)$ and $(1, 0)$. This is a one-to-one enumeration, and the inverse functions are (primitive) recursive—but we do not require at the present any notation for them.

**Lean 4**

- [DataTypesAsLattices/Continuous/theorem_1_1.lean](theorem_1_1.lean)
