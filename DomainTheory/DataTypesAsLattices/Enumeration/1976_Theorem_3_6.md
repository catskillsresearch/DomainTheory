# Theorem 3.6

**THEOREM 3.6 (The subalgebra theorem).** *The enumeration degrees are exactly the finitely generated combinatory subalgebras of* $\mathbf{P}\omega$.

By “subalgebras” here we of course mean subsets containing $\mathbf{G}$ and closed under application (hence, they contain all of $\mathbf{RE}$, the least subalgebra). Part of the assertion is that every finitely generated subalgebra has a single generator (under application). This fact is an easy extension of Theorem 3.1. Not very much seems to be known about enumeration degrees. Joins can obviously be formed using the pairing function $\langle x, y \rangle$ on sets. Each degree is a countable set; hence, it is trivial to obtain the existence of a sequence of degrees whose *infinite join* is not a degree (not finitely generated). The intersection of subalgebras is a subalgebra—but it may not be a degree even starting with degrees. There are no minimal degrees above $\mathbf{RE}$, but there are minimal *pairs* of degrees. Also for a given degree there are only countably many degrees minimal over it; but the question of whether the partial ordering of enumeration degrees is dense seems still to be open.

Theorem 3.6 shows that the semilattice of enumeration degrees is naturally extendable to a *complete lattice* (the lattice of all subalgebras of $\mathbf{P}\omega$), but whether there is anything interesting to say about this complete lattice from the point of view of structure is not at all clear. Rogers has shown (1967, pp. 151–153) that Turing degrees can be defined in terms of enumeration degrees by restricting to special elements. In our style of notation we would define the space:

$$\mathbf{TOT} = \{u \mid u = \mathbf{\$}(u) \text{ and } \forall n \in \omega.\, u(n) \in \omega\},$$

the space of all graphs of total functions. Then the system $\{\mathbf{Deg}(u) \mid u \in \mathbf{TOT}\}$ is isomorphic to the system of Turing degrees. Now there are many other interesting subsets of $\mathbf{P}\omega$. Whether the degree structure of these various subsets is worth investigation is a question whose answer awaits some new ideas.

Among the subsets of $\mathbf{P}\omega$ with natural mathematical structure, we of course have $\mathbf{FUN}$, which is a semigroup under $\circ = \lambda u \lambda v \lambda x.\, u(v(x))$. It is, however, a rather complicated semigroup. We introduce for its study three new combinators:

$$(3.13) \quad \mathbf{R} = \lambda x.\, \langle 0, x \rangle;$$

$$(3.14) \quad \mathbf{L} = \lambda x.\, x_1(x_2);$$

$$(3.15) \quad \bar{u} = \lambda x.\, x_0 \supset \langle 1, u, x_1 \rangle,\, \overline{u(x_1)(x_2)}.$$

**Lean 4**

- [DataTypesAsLattices/Enumeration/theorem_3_6.lean](theorem_3_6.lean)
- [DataTypesAsLattices/Enumeration/theorem_3_6_converse.lean](theorem_3_6_converse.lean)
- [DataTypesAsLattices/Enumeration/theorem_3_6_degree.lean](theorem_3_6_degree.lean)
- [DataTypesAsLattices/Enumeration/theorem_3_6_finite.lean](theorem_3_6_finite.lean)
- [DataTypesAsLattices/Enumeration/theorem_3_6_generated.lean](theorem_3_6_generated.lean)
