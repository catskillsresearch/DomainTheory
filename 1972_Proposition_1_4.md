# Proposition 1.4

We now have a large number of injective spaces, and further examples could be found using the next fact.

**1.4 Proposition.** A retract of an injective space is injective.

**Proof:** Let $D$ be injective. By a retract of $D$ we understand a subspace $D' \subseteq D$ for which there exists a retraction map $j: D \to D'$ such that

$$
D' = x \in D : j(x) = x.
$$

Then if $f: X \to D'$ and $X \subseteq Y$, we have $f: X \to D$ as a continuous map also. Taking $\bar{f}: Y \to D$, we have only to form

$$
j \circ \bar{f} : Y \to D'
$$

to show that $D'$ is injective. $\square$

**Lean 4**

- [ContinuousLattice/Injective/IsInjectiveSpaceu2eof_retract.lean](DomainTheory/ContinuousLattice/Injective/IsInjectiveSpaceu2eof_retract.lean)
- [ContinuousLattice/Injective/IsRetractSubspace.lean](DomainTheory/ContinuousLattice/Injective/IsRetractSubspace.lean)
- [ContinuousLattice/Injective/proposition_1_4.lean](DomainTheory/ContinuousLattice/Injective/proposition_1_4.lean)
