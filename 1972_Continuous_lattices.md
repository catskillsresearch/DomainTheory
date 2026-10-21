# Continuous lattices

**2. CONTINUOUS LATTICES.** Every $T_0$-space becomes a partially ordered set under the definition:

$$
x \sqsubseteq y \text{ iff whenever } x \in U \text{ and } U \text{ is open, then } y \in U.
$$

Indeed, though this relation is reflexive and transitive, the condition that it be *antisymmetric* is exactly equivalent to the $T_0$-axiom.

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

By a directed subset of $X$ we of course mean that it is directed in the sense of the partial ordering $\sqsubseteq$. Note that in this paper directed sets are always *non-empty*. The sets satisfying (i) and (ii) form the *induced topology* on a partially ordered set $X$, which is still a $T_0$-space because the sets $x \in X : x \not\sqsubseteq y$ remain open even in the sense of (ii). Obviously a directed set $S \subseteq X$ can be regarded as a net, and now in view of (ii) it follows that $S$ converges to $\bigsqcup S$ — if this lub exists. We can summarize this discussion as follows.

- [Proposition 2.1](1972_Proposition_2_1.md)
- [Proposition 2.2](1972_Proposition_2_2.md)
- [Definition 2.3](1972_Definition_2_3.md)
- [Proposition 2.4](1972_Proposition_2_4.md)
- [Proposition 2.5](1972_Proposition_2_5.md)
- [Proposition 2.6](1972_Proposition_2_6.md)
- [Proposition 2.7](1972_Proposition_2_7.md)
- [Proposition 2.8](1972_Proposition_2_8.md)
- [Proposition 2.9](1972_Proposition_2_9.md)
- [Proposition 2.10](1972_Proposition_2_10.md)
- [Proposition 2.11](1972_Proposition_2_11.md)
- [Theorem 2.12](1972_Theorem_2_12.md)

The lattice approach to injective spaces gives a completely "internal" characterization of them: in the first place the lattices are complete. Next we can define lattice theoretically:

$$
x \ll y \quad \text{iff} \quad \text{whenever } y \sqsubseteq \bigsqcup Z \text{ and } Z \subseteq D \text{ is directed,}
$$

then $x \sqsubseteq z$ for some $z \in Z$.

Finally we assume that for all $y \in D$:

$$y = \bigsqcup  x \in D : x \ll y .$$

That makes $D$ a continuous lattice with the sets $ y \in D : x \ll y $ as a basis for the topology. Such $T_0$-spaces are injective and every injective space can be obtained in this way with the lattice structure being uniquely determined by the topology. Furthermore, as we have seen, the injective property can be exhibited, as in the proof of 2.11, by an explicit formula for extending functions.

The retract approach to injective spaces should also be considered. The Cartesian powers $\mathbb{O}^I$ are very simple spaces; indeed, as lattices these are just the Boolean algebras of *all subsets* of $I$ (that is, isomorphic thereto). The topology has as a basis the

classes of sets containing given finite sets (the *weak topology*, cf. Nerode (1959)). A continuous function

$$j : \mathcal{P}I \to \mathcal{P}I$$

is one of "finite character" so that

$$j(X) = \bigcup  j(F) : F \subseteq X $$

where $X \subseteq I$ and $F$ ranges over *finite sets*. Such a function $j$ is a *retraction* iff it is an *idempotent*:

$$j \circ j = j,$$

which means that the range of $j$ is the set of fixed points of $j$. As we have seen

$$D =  X \in \mathcal{P}I : j(X) = X $$

is a continuous lattice (under $\subseteq$ in this case), and *every* continuous lattice is isomorphic to one obtained in this way. This provides a representation theorem of sorts for continuous lattices, but it does not seem to be of too much help in proving theorems.

The reader should not forget that any space (any *given* number of spaces $X$, $Y$, $\ldots$) can be found as a *subspace* of a continuous lattice $D$. Since $D$ is injective any continuous function $f : X \to Y$ can be extended to a continuous function $\bar{f} : D \to D$. Thus the continuous functions from $D$ into $D$ are a rich totality including *all* the structure of continuous functions on *all* the subspaces. And this remark brings us to the study of function spaces.

**Lean 4**

- [ContinuousLattice/Constructions.lean](DomainTheory/ContinuousLattice/Constructions.lean)
- [ContinuousLattice/Constructions/Basic.lean](DomainTheory/ContinuousLattice/Constructions/Basic.lean)
- [ContinuousLattice/Constructions/continuous_eq_sSup_openInfs.lean](DomainTheory/ContinuousLattice/Constructions/continuous_eq_sSup_openInfs.lean)
- [ContinuousLattice/Constructions/directedOn_finite_sSup_mem.lean](DomainTheory/ContinuousLattice/Constructions/directedOn_finite_sSup_mem.lean)
- [ContinuousLattice/Constructions/isContinuousLattice_prop.lean](DomainTheory/ContinuousLattice/Constructions/isContinuousLattice_prop.lean)
- [ContinuousLattice/Constructions/scottExtend.lean](DomainTheory/ContinuousLattice/Constructions/scottExtend.lean)
- [ContinuousLattice/Constructions/scottExtend_aux_directed.lean](DomainTheory/ContinuousLattice/Constructions/scottExtend_aux_directed.lean)
- [ContinuousLattice/Constructions/scottExtend_aux_nonempty.lean](DomainTheory/ContinuousLattice/Constructions/scottExtend_aux_nonempty.lean)
- [ContinuousLattice/Constructions/scottExtend_continuous.lean](DomainTheory/ContinuousLattice/Constructions/scottExtend_continuous.lean)
- [ContinuousLattice/Constructions/scottExtend_eq_of_continuous.lean](DomainTheory/ContinuousLattice/Constructions/scottExtend_eq_of_continuous.lean)
- [ContinuousLattice/Constructions/scottExtend_maximal.lean](DomainTheory/ContinuousLattice/Constructions/scottExtend_maximal.lean)
- [ContinuousLattice/Constructions/scottExtend_maximal_le.lean](DomainTheory/ContinuousLattice/Constructions/scottExtend_maximal_le.lean)
- [ContinuousLattice/Constructions/scottTopology_prop.lean](DomainTheory/ContinuousLattice/Constructions/scottTopology_prop.lean)
- [ContinuousLattice/Constructions/scottTopology_sierpinskiPower.lean](DomainTheory/ContinuousLattice/Constructions/scottTopology_sierpinskiPower.lean)
- [ContinuousLattice/Constructions/sierpinskiPower_isContinuousLattice.lean](DomainTheory/ContinuousLattice/Constructions/sierpinskiPower_isContinuousLattice.lean)
- [ContinuousLattice/Constructions/sierpinski_isInjective_and_isContinuousLattice.lean](DomainTheory/ContinuousLattice/Constructions/sierpinski_isInjective_and_isContinuousLattice.lean)
- [ContinuousLattice/ScottMaps.lean](DomainTheory/ContinuousLattice/ScottMaps.lean)
- [ContinuousLattice/ScottMaps/Basic.lean](DomainTheory/ContinuousLattice/ScottMaps/Basic.lean)
- [ContinuousLattice/ScottMaps/PreservesDirectedSup.lean](DomainTheory/ContinuousLattice/ScottMaps/PreservesDirectedSup.lean)
- [ContinuousLattice/ScottMaps/continuous_of_preservesDirectedSup.lean](DomainTheory/ContinuousLattice/ScottMaps/continuous_of_preservesDirectedSup.lean)
- [ContinuousLattice/ScottMaps/continuous_preservesDirectedSup.lean](DomainTheory/ContinuousLattice/ScottMaps/continuous_preservesDirectedSup.lean)
- [ContinuousLattice/ScottMaps/meet_preservesDirectedSup.lean](DomainTheory/ContinuousLattice/ScottMaps/meet_preservesDirectedSup.lean)
- [ContinuousLattice/ScottMaps/preservesDirectedSup_monotone.lean](DomainTheory/ContinuousLattice/ScottMaps/preservesDirectedSup_monotone.lean)
- [ContinuousLattice/ScottMaps/scottOpen_preimage.lean](DomainTheory/ContinuousLattice/ScottMaps/scottOpen_preimage.lean)
- [ContinuousLattice/Specialization.lean](DomainTheory/ContinuousLattice/Specialization.lean)
- [ContinuousLattice/Specialization/Basic.lean](DomainTheory/ContinuousLattice/Specialization/Basic.lean)
- [ContinuousLattice/Specialization/IsMonotoneNet.lean](DomainTheory/ContinuousLattice/Specialization/IsMonotoneNet.lean)
- [ContinuousLattice/Specialization/ScottConvergesTo.lean](DomainTheory/ContinuousLattice/Specialization/ScottConvergesTo.lean)
- [ContinuousLattice/Specialization/ScottOpen_iff_dirSupInacc.lean](DomainTheory/ContinuousLattice/Specialization/ScottOpen_iff_dirSupInacc.lean)
- [ContinuousLattice/Specialization/SpecializationLe.lean](DomainTheory/ContinuousLattice/Specialization/SpecializationLe.lean)
- [ContinuousLattice/Specialization/SpecializationLeu2emap.lean](DomainTheory/ContinuousLattice/Specialization/SpecializationLeu2emap.lean)
- [ContinuousLattice/Specialization/isOpen_iff_scottOpen.lean](DomainTheory/ContinuousLattice/Specialization/isOpen_iff_scottOpen.lean)
- [ContinuousLattice/Specialization/isOpen_scott_iff_scottOpen.lean](DomainTheory/ContinuousLattice/Specialization/isOpen_scott_iff_scottOpen.lean)
- [ContinuousLattice/Specialization/scottOpen_not_le.lean](DomainTheory/ContinuousLattice/Specialization/scottOpen_not_le.lean)
- [ContinuousLattice/Specialization/scottTopologicalSpace.lean](DomainTheory/ContinuousLattice/Specialization/scottTopologicalSpace.lean)
- [ContinuousLattice/Specialization/scottTopology_t0Space.lean](DomainTheory/ContinuousLattice/Specialization/scottTopology_t0Space.lean)
- [ContinuousLattice/Specialization/specializationLe_antisymm.lean](DomainTheory/ContinuousLattice/Specialization/specializationLe_antisymm.lean)
- [ContinuousLattice/Specialization/specializationLe_iff_specializes.lean](DomainTheory/ContinuousLattice/Specialization/specializationLe_iff_specializes.lean)
- [ContinuousLattice/Specialization/specializationLe_scott_iff.lean](DomainTheory/ContinuousLattice/Specialization/specializationLe_scott_iff.lean)
- [ContinuousLattice/Specialization/specializationPreorder.lean](DomainTheory/ContinuousLattice/Specialization/specializationPreorder.lean)
- [ContinuousLattice/WayBelow.lean](DomainTheory/ContinuousLattice/WayBelow.lean)
- [ContinuousLattice/WayBelow/Basic.lean](DomainTheory/ContinuousLattice/WayBelow/Basic.lean)
- [ContinuousLattice/WayBelow/Basic/notation5.lean](DomainTheory/ContinuousLattice/WayBelow/Basic/notation5.lean)
- [ContinuousLattice/WayBelow/IsContinuousLattice.lean](DomainTheory/ContinuousLattice/WayBelow/IsContinuousLattice.lean)
- [ContinuousLattice/WayBelow/IsContinuousLatticeu2esSup_wayBelow.lean](DomainTheory/ContinuousLattice/WayBelow/IsContinuousLatticeu2esSup_wayBelow.lean)
- [ContinuousLattice/WayBelow/ScottOpen.lean](DomainTheory/ContinuousLattice/WayBelow/ScottOpen.lean)
- [ContinuousLattice/WayBelow/ScottOpenu2eisUpperSet.lean](DomainTheory/ContinuousLattice/WayBelow/ScottOpenu2eisUpperSet.lean)
- [ContinuousLattice/WayBelow/WayBelow.lean](DomainTheory/ContinuousLattice/WayBelow/WayBelow.lean)
- [ContinuousLattice/WayBelow/WayBelowu2ele.lean](DomainTheory/ContinuousLattice/WayBelow/WayBelowu2ele.lean)
- [ContinuousLattice/WayBelow/WayBelowu2ele_trans.lean](DomainTheory/ContinuousLattice/WayBelow/WayBelowu2ele_trans.lean)
- [ContinuousLattice/WayBelow/WayBelowu2esup.lean](DomainTheory/ContinuousLattice/WayBelow/WayBelowu2esup.lean)
- [ContinuousLattice/WayBelow/WayBelowu2etrans_le.lean](DomainTheory/ContinuousLattice/WayBelow/WayBelowu2etrans_le.lean)
- [ContinuousLattice/WayBelow/bot_wayBelow.lean](DomainTheory/ContinuousLattice/WayBelow/bot_wayBelow.lean)
- [ContinuousLattice/WayBelow/directedOn_wayBelow.lean](DomainTheory/ContinuousLattice/WayBelow/directedOn_wayBelow.lean)
- [ContinuousLattice/WayBelow/exists_wayBelow_Ici_subset.lean](DomainTheory/ContinuousLattice/WayBelow/exists_wayBelow_Ici_subset.lean)
- [ContinuousLattice/WayBelow/exists_wayBelow_subset.lean](DomainTheory/ContinuousLattice/WayBelow/exists_wayBelow_subset.lean)
- [ContinuousLattice/WayBelow/isContinuousLattice_iff_isLUB_sInf_nhds.lean](DomainTheory/ContinuousLattice/WayBelow/isContinuousLattice_iff_isLUB_sInf_nhds.lean)
- [ContinuousLattice/WayBelow/sInf_wayBelow.lean](DomainTheory/ContinuousLattice/WayBelow/sInf_wayBelow.lean)
- [ContinuousLattice/WayBelow/scottOpen_inter.lean](DomainTheory/ContinuousLattice/WayBelow/scottOpen_inter.lean)
- [ContinuousLattice/WayBelow/scottOpen_sUnion.lean](DomainTheory/ContinuousLattice/WayBelow/scottOpen_sUnion.lean)
- [ContinuousLattice/WayBelow/scottOpen_univ.lean](DomainTheory/ContinuousLattice/WayBelow/scottOpen_univ.lean)
- [ContinuousLattice/WayBelow/scottOpen_wayBelow.lean](DomainTheory/ContinuousLattice/WayBelow/scottOpen_wayBelow.lean)
- [ContinuousLattice/WayBelow/wayBelow_interpolate.lean](DomainTheory/ContinuousLattice/WayBelow/wayBelow_interpolate.lean)
- [ContinuousLattice/WayBelow/wayBelow_sSup_iff.lean](DomainTheory/ContinuousLattice/WayBelow/wayBelow_sSup_iff.lean)
- [ContinuousLattice/WayBelow/wayBelow_self_iff_scottOpen_Ici.lean](DomainTheory/ContinuousLattice/WayBelow/wayBelow_self_iff_scottOpen_Ici.lean)
