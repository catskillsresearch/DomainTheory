# Proposition 2.7

One of the justifications (by euphony at least) of the term *continuous lattice* is the fact that such spaces allow for so many continuous functions. One indication of this is the result:

**2.7 Proposition.** *In a continuous lattice $D$ the finitary lattice operations $\sqcup$ and $\sqcap$ are continuous.*

**Proof:** It is trivial to show that $\sqcup$ is continuous in every complete lattice; this is not so for $\sqcap$. In view of 2.6 we need only show

$$
x \sqcap \bigsqcup S = \bigsqcup x \sqcap y : y \in S
$$

for every directed $S \subseteq D$. In fact it is enough to show

$$
x \sqcap \bigsqcup S \sqsubseteq \bigsqcup x \sqcap y : y \in S
$$

because the opposite inequality is valid in all complete lattices. In view of the fact that $D$ is continuous, it is enough to show that

$$
t \ll x \sqcap \bigsqcup S \text{ implies } t \sqsubseteq \bigsqcup x \sqcap y : y \in S.
$$

So assume $t \ll x \sqcap \bigsqcup S$. Then $t \sqsubseteq x \sqcap \bigsqcup S \sqsubseteq x$. Also $t \ll \bigsqcup S$ because $x \sqcap \bigsqcup S \sqsubseteq \bigsqcup S$. Thus $t \ll y$ for some $y \in S$ since the set

$$
z \in D : t \ll z
$$

is open. But then $t \sqsubseteq y$, and so $t \sqsubseteq x \sqcap y$, and the result follows. $\square$

**Lean 4**

- [ContinuousLattice/ScottMaps/proposition_2_7_inf_left.lean](DomainTheory/ContinuousLattice/ScottMaps/proposition_2_7_inf_left.lean)
- [ContinuousLattice/ScottMaps/proposition_2_7_inf_right.lean](DomainTheory/ContinuousLattice/ScottMaps/proposition_2_7_inf_right.lean)
- [ContinuousLattice/ScottMaps/proposition_2_7_sup.lean](DomainTheory/ContinuousLattice/ScottMaps/proposition_2_7_sup.lean)
