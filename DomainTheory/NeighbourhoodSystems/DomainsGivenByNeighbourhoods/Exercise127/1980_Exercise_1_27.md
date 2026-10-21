# Exercise 1.27

**EXERCISE 1.27.** Further closure properties of domains can be proved for bounded sets. We say $X \subseteq |\mathcal{D}|$ is *bounded* iff for some $y \in |\mathcal{D}|$ we have $x \subseteq y$ for all $x \in X$. This $y$ is called an *upper bound*. We let

$$
\bigsqcup X = \bigcap \{y \in |\mathcal{D}| \mid x \subseteq y \text{ all } x \in X\}.
$$

Prove that if $X$ is bounded, then $\bigsqcup X$ is the *least upper bound* for $X$ in $|\mathcal{D}|$. Prove also: if $U, V \in \mathcal{D}$ are neighbourhoods, then $\{U, V\}$ is consistent in $\mathcal{D}$ iff $\{\uparrow U, \uparrow V\}$ is bounded in $|\mathcal{D}|$. (That is, boundedness is for elements what consistency is for neighbourhoods.) Prove finally with the aid of 1.18 that $X \subseteq |\mathcal{D}|$ is bounded iff every finite subset of $X$ is bounded.

**Lean 4**

- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise127.lean](../Exercise127.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise127/Basic.lean](Basic.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise127/Bounded.lean](Bounded.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise127/bounded_iff_finite_bounded.lean](bounded_iff_finite_bounded.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise127/consistent_pair_iff_bounded.lean](consistent_pair_iff_bounded.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise127/interUpTo_pairSeq.lean](interUpTo_pairSeq.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise127/le_sSup.lean](le_sSup.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise127/pairSeq.lean](pairSeq.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise127/sSup.lean](sSup.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise127/sSup_le.lean](sSup_le.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise127/upperBounds.lean](upperBounds.lean)
- [NeighbourhoodSystems/DomainsGivenByNeighbourhoods/Exercise127/upperBounds_nonempty.lean](upperBounds_nonempty.lean)
