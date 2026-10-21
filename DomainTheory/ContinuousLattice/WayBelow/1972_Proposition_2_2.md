# Proposition 2.2

Our main interest will lie with those partially ordered sets in which every subset has a lub: namely, *complete lattices*. If $D$ is such a space we write $\bot = \bigsqcup \emptyset$ and $\top = \bigsqcup D$ for the smallest and largest elements (read: bottom and top). As is well known, greatest lower bounds must exist, for:

$$
\sqcap S = \bigsqcup x \in D : x \sqsubseteq y \text{ for all } y \in S
$$

gives the definition.

**Complete lattice.** There is no local definition. `WayBelow`, defined below, and `IsContinuousLattice` in [Definition 2.3](1972_Definition_2_3.md) assume Mathlib’s `CompleteLattice` typeclass, as do the propositions of this section. That is the “lattices are complete” sentence.

Given a complete lattice $D$ we define

$$
x \ll y \text{ iff } y \in \text{Int}z \in D : x \sqsubseteq z,
$$

where the interior is taken in the sense of the induced topology. The relation $x \ll y$ behaves somewhat like a strict ordering relation; at least its meaning is clearly that $y$ should be definitely larger than $x$ in the partial ordering. Such a relation has many pleasant properties.

The primary purpose of introducing it is to provide a simple definition for the kind of spaces that are most useful to us. We first mention the most elementary features of this relation.

**2.2 Proposition.** In a complete lattice $D$ we have:

(i) $\bot \ll x$;

(ii) $x \ll z$ and $y \ll z$ imply $x \sqcup y \ll z$;

(iii) $x \ll y \sqsubseteq z$ implies $x \ll z$;

(iv) $x \sqsubseteq y \ll z$ implies $x \ll z$;

(v) $x \ll y$ implies $x \sqsubseteq y$;

(vi) $x \ll x$ iff $z \in D : x \sqsubseteq z$ is open;

(vii) if $S \subseteq D$ is directed, then $x \ll \bigsqcup S$ iff $x \ll y$ for some $y \in S$. $\square$

The lattice approach to injective spaces gives a completely "internal" characterization of them: in the first place the lattices are complete. Next we can define lattice theoretically:

$$
x \ll y \quad \text{iff} \quad \text{whenever } y \sqsubseteq \bigsqcup Z \text{ and } Z \subseteq D \text{ is directed,}
$$

then $x \sqsubseteq z$ for some $z \in Z$.

`WayBelow` is the interior definition above. Clause (vii) is `wayBelow_sSup_iff`. The equation that turns this relation into a continuous lattice is [Definition 2.3](1972_Definition_2_3.md).

**Lean 4**

- [ContinuousLattice/WayBelow.lean](../WayBelow.lean)
- [ContinuousLattice/WayBelow/Basic.lean](Basic.lean)
- [ContinuousLattice/WayBelow/Basic/notation5.lean](Basic/notation5.lean)
- [ContinuousLattice/WayBelow/WayBelow.lean](WayBelow.lean)
- [ContinuousLattice/WayBelow/bot_wayBelow.lean](bot_wayBelow.lean)
- [ContinuousLattice/WayBelow/WayBelowu2esup.lean](WayBelowu2esup.lean)
- [ContinuousLattice/WayBelow/WayBelowu2etrans_le.lean](WayBelowu2etrans_le.lean)
- [ContinuousLattice/WayBelow/WayBelowu2ele_trans.lean](WayBelowu2ele_trans.lean)
- [ContinuousLattice/WayBelow/WayBelowu2ele.lean](WayBelowu2ele.lean)
- [ContinuousLattice/WayBelow/wayBelow_self_iff_scottOpen_Ici.lean](wayBelow_self_iff_scottOpen_Ici.lean)
- [ContinuousLattice/WayBelow/scottOpen_wayBelow.lean](scottOpen_wayBelow.lean)
- [ContinuousLattice/WayBelow/wayBelow_sSup_iff.lean](wayBelow_sSup_iff.lean)
