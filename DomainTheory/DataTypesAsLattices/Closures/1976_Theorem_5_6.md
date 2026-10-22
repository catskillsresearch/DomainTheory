# Theorem 5.6

**THEOREM 5.6 (The limit theorem for algebraic lattices).**

$$(\lambda f : \mathbf{V} \circ\to \mathbf{V}.\, \mathbf{Y}(f)) : (\mathbf{V} \circ\to \mathbf{V}) \circ\to \mathbf{V}.$$

In words: if $f$ is a mapping on closure operations, then its least fixed point is also a closure operation. The proof of course holds with any retract in place of $\mathbf{V}$, but we are more interested in applications to $\mathbf{V}$. For example, note that $\mathbf{V}(\bot) = \mathbf{I}$. Now let $f = \lambda a : \mathbf{V}.\, a \circ\to a$. The least fixed point of this $f$ is the limit of the sequence:

$$\bot,\, \mathbf{I},\, \mathbf{I} \circ\to \mathbf{I},\, (\mathbf{I} \circ\to \mathbf{I}) \circ\to (\mathbf{I} \circ\to \mathbf{I}),\, ((\mathbf{I} \circ\to \mathbf{I}) \circ\to (\mathbf{I} \circ\to \mathbf{I})) \circ\to ((\mathbf{I} \circ\to \mathbf{I}) \circ\to (\mathbf{I} \circ\to \mathbf{I})),\, \ldots$$
and we see that all these retracts are *strict*. This means $\mathbf{Y}(f)$ is nontrivial in that it has at least *two* fixed points (viz., $\bot$ and $\top$). But $d = \mathbf{Y}(f)$ must be the least closure operation satisfying

$$(5.25) \quad d = d \circ\to d,$$

and we have thus proved that there are *nontrivial* algebraic lattices isomorphic to their own function spaces. This construction (which rests on hardly more than (5.2), since we could take $d = \mathbf{Y}(\lambda a.\, \mathbf{I} \cup (a \circ\to a))$) is much quicker than the inverse limit construction originally found by the author to give $\lambda$-calculus models satisfying $(\eta)$. There are many other fixed points of (5.25) besides this least closure operation, but their connection with inverse limits is not fully investigated.

We note in conclusion that most constructions by fixed points give algebraic lattices (like **lamb** in § 4), and so we could just as well do them in $\mathbf{V}$ if we remember to use $\boxtimes$ and $\boxplus$. The one-point space is $\top$ (*not* **nil**), and so the connection with inverse limits via Theorem 4.6 is not as clear when nonstrict functions are used. For many purposes, this may not make any difference.

**Lean 4**

- [DataTypesAsLattices/Closures/theorem_5_6.lean](theorem_5_6.lean)
- [DataTypesAsLattices/Closures/theorem_5_6_combinator.lean](theorem_5_6_combinator.lean)
- [DataTypesAsLattices/Closures/theorem_5_6_iterates.lean](theorem_5_6_iterates.lean)
- [DataTypesAsLattices/Closures.lean](../Closures.lean)
