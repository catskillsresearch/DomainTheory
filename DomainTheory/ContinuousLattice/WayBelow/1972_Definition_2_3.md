# Definition 2.3

The proofs of these statements can be safely left to the reader.

**2.3 Definition.** A *continuous lattice* is a complete lattice $D$ in which for every $y \in D$ we have:

$$
y = \bigsqcup x \in D : x \ll y.
$$

**Continuous lattice.** `IsContinuousLattice` is this definition: every element is the least upper bound of the elements way below it. It is a hypothesis of [Proposition 2.7](../ScottMaps/1972_Proposition_2_7.md), [Proposition 2.8](../Constructions/1972_Proposition_2_8.md), [Proposition 2.9](../Constructions/1972_Proposition_2_9.md), and [Proposition 2.11](../Constructions/1972_Proposition_2_11.md), of [Theorem 2.12](../Theorem212/1972_Theorem_2_12.md), and of the later projection and inverse-limit proofs. The sets $ y \in D : x \ll y $ are a basis for the topology.

As an alternate definition we find [Proposition 2.4](1972_Proposition_2_4.md).

**Lean 4**

- [ContinuousLattice/WayBelow/IsContinuousLattice.lean](IsContinuousLattice.lean)
- [ContinuousLattice/WayBelow/IsContinuousLatticeu2esSup_wayBelow.lean](IsContinuousLatticeu2esSup_wayBelow.lean)
- [ContinuousLattice/WayBelow/directedOn_wayBelow.lean](directedOn_wayBelow.lean)
