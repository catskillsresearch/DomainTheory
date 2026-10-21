# Specialization

Scott assumes the $T_0$ separation axiom throughout; for what that means in the paper and in Lean, see [T0 spaces](../Injective/1972_T0_spaces.md). Here we use $T_0$ only as background for the specialization order and Scott topology.

Every $T_0$-space becomes a partially ordered set under the definition:

$$
x \sqsubseteq y \text{ iff whenever } x \in U \text{ and } U \text{ is open, then } y \in U.
$$

Indeed, though this relation is reflexive and transitive, the condition that it be *antisymmetric* is exactly equivalent to the $T_0$-axiom (formalized in Lean as `specializationLe_antisymm`).

In the converse direction, every partially ordered set $\langle X, \sqsubseteq \rangle$ can be so obtained, for we have only to define $U \subseteq X$ as being open if it satisfies the condition:

(i) whenever $x \in U$ and $x \sqsubseteq y$, then $y \in U$.

The axioms for partial order make $X$ a $T_0$-space, because for any $y \in X$ the set

$$
x \in X : x \not\sqsubseteq y
$$

is open. This connection is not very interesting, however.

What *is* interesting in topological spaces is *convergence* and the properties of *limit points*. We shall discuss limits in terms of *nets*, in particular in terms of *monotone nets*. A monotone net in a $T_0$-space $X$ is a function

$$
x : I \to X
$$

where $\langle I, \le \rangle$ is a directed set and where $i \le j$ implies $x_i \sqsubseteq x_j$ for all $i, j \in I$. In a $T_1$-space a monotone net is constant (hence, uninteresting) because the $\sqsubseteq$-relation is the identity. As usual (cf. Kelley (1955), p.66) we say that a net $x$ *converges* to an element $y$ iff whenever $U$ is open and $y \in U$, then for some $i \in I$ we have $x_j \in U$ for all $j \ge i$. Note that a monotone net $x$ converges to each of its terms $x_i$. Suppose that a monotone net $x$ converges to an element $y$ which is an upper bound to all the terms of $x$. Then $y$ must be the *least upper bound*, which we write as:

$$
y = \bigsqcup x_i : i \in I.
$$

To see this, assume that $z$ is any other upper bound with $x_i \sqsubseteq z$ for all $i \in I$. If $U$ is open and $y \in U$, then $x_i \in U$ for some $i \in I$. But then $z \in U$, and so $y \sqsubseteq z$ follows.

We shall find that most of the facts about the topology of the spaces we are concerned with here can be expressed in terms of least upper bounds (lubs). It is not always the case, however, that lubs are limits. Thus, for a partially ordered set $X$, we impose a further restriction on its topology beyond condition (i) for saying when a subset $U$ is open:

(ii) whenever $S \subseteq X$ is *directed*, $\bigsqcup S$ exists, and $\bigsqcup S \in U$, then $S \cap U \neq \emptyset$.

By a directed subset of $X$ we of course mean that it is directed in the sense of the partial ordering $\sqsubseteq$. Note that in this paper directed sets are always *non-empty*. The sets satisfying (i) and (ii) form the *induced topology* on a partially ordered set $X$, which is still a $T_0$-space because the sets $x \in X : x \not\sqsubseteq y$ remain open even in the sense of (ii). Obviously a directed set $S \subseteq X$ can be regarded as a net, and now in view of (ii) it follows that $S$ converges to $\bigsqcup S$ — if this lub exists.

**Lean 4**

- [ContinuousLattice/Specialization.lean](../Specialization.lean)
- [ContinuousLattice/Specialization/Basic.lean](Basic.lean)
- [ContinuousLattice/Specialization/SpecializationLe.lean](SpecializationLe.lean)
- [ContinuousLattice/Specialization/specializationLe_iff_specializes.lean](specializationLe_iff_specializes.lean)
- [ContinuousLattice/Specialization/specializationLe_antisymm.lean](specializationLe_antisymm.lean)
- [ContinuousLattice/Specialization/SpecializationLeu2emap.lean](SpecializationLeu2emap.lean)
- [ContinuousLattice/Specialization/specializationPreorder.lean](specializationPreorder.lean)
- [ContinuousLattice/Specialization/IsMonotoneNet.lean](IsMonotoneNet.lean)
- [ContinuousLattice/Specialization/ScottConvergesTo.lean](ScottConvergesTo.lean)
- [ContinuousLattice/Specialization/scottTopologicalSpace.lean](scottTopologicalSpace.lean)
- [ContinuousLattice/Specialization/specializationLe_scott_iff.lean](specializationLe_scott_iff.lean)
- [ContinuousLattice/Specialization/scottOpen_not_le.lean](scottOpen_not_le.lean)
- [ContinuousLattice/Specialization/ScottOpen_iff_dirSupInacc.lean](ScottOpen_iff_dirSupInacc.lean)
- [ContinuousLattice/Specialization/isOpen_iff_scottOpen.lean](isOpen_iff_scottOpen.lean)
- [ContinuousLattice/Specialization/isOpen_scott_iff_scottOpen.lean](isOpen_scott_iff_scottOpen.lean)
- [ContinuousLattice/WayBelow/ScottOpen.lean](../WayBelow/ScottOpen.lean)
- [ContinuousLattice/WayBelow/ScottOpenu2eisUpperSet.lean](../WayBelow/ScottOpenu2eisUpperSet.lean)
- [ContinuousLattice/WayBelow/scottOpen_univ.lean](../WayBelow/scottOpen_univ.lean)
- [ContinuousLattice/WayBelow/scottOpen_inter.lean](../WayBelow/scottOpen_inter.lean)
- [ContinuousLattice/WayBelow/scottOpen_sUnion.lean](../WayBelow/scottOpen_sUnion.lean)
