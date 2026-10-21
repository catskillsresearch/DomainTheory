# Theorem 7.1

**THEOREM 7.1 (The closure theorem).** *If $A$ and $B$ are restricted equivalence relations, then so are $A \to B$, $A \times B$ and $A + B$. We find:*

(i) $f : A \to B$ iff $f = \lambda x.\, f(x)$ and whenever $x \, A \, y$, then $f(x) \, B \, f(y)$, in particular:

(ii) if $f : A \to B$ and $x : A$, then $f(x) : B$; furthermore,

(iii) $u : A \times B$ iff $u = \langle u_0, u_1 \rangle$ and $u_0 : A$ and $u_1 : B$;

(iv) $u : A + B$ iff either $u = \langle 0, u_1 \rangle$ and $u_1 : A$ or $u = \langle 1, u_1 \rangle$ and $u_1 : B$.

It follows easily from (7.1) that the restricted equivalence relations form a Cartesian closed category which—in distinction to the category of retracts—has disjoint sums (or coproducts as they are usually called in category theory). This result is probably a special case of a more general theorem. The point is that $\mathbf{P}\omega$ itself is a space in a Cartesian closed category (that of continuous lattices and continuous maps) and it contains as subspaces the Boolean space and especially its own function space and Cartesian square. In this circumstance any such rich space must be such that its restricted equivalence relations again form a good category. Our construction is not strictly categorical in nature, as we have used the elements of $\mathbf{P}\omega$ and have relied on being able to form arbitrary subsets (arbitrary relations). But a more abstract formulation must be possible. The connection with the category of retracts is indicated in the next theorem.

**Lean 4**

- [DataTypesAsLattices/Functionality/theorem_7_1.lean](theorem_7_1.lean)
