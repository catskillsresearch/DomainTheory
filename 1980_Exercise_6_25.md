# Exercise 6.25

**EXERCISE 6.25.** For a projection pair $g : \mathcal{D} \to \mathcal{E}$ and $h : \mathcal{E} \to \mathcal{D}$ show that for $x \in |\mathcal{D}|$ and $y \in |\mathcal{E}|$ we have:

$$g(x) \sqsubseteq y \text{ iff } x \sqsubseteq h(y).$$

Thus, conclude that:

$$h(y) = \bigsqcup \{x \in |\mathcal{D}| \mid g(x) \sqsubseteq y\}, \quad \text{and}$$

$$g(x) = \bigsqcap \{y \in |\mathcal{E}| \mid x \sqsubseteq h(y)\},$$

for all $x \in |\mathcal{D}|$ and $y \in |\mathcal{E}|$. So each of the functions determines the other. In the first equation check that the set on the right is directed, and in the second equation that the set on the right is non empty. Prove also that $g$ maps consistent sets to consistent sets and preserves $\bigsqcup$ (not just directed unions).

**Lean 4**

- [NeighbourhoodSystems/DomainEquations/Exercise625.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise625.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise625/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise625/Basic.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise625/galois.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise625/galois.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise625/inj_bounded.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise625/inj_bounded.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise625/inj_eq_sInf.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise625/inj_eq_sInf.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise625/inj_proj_apply_le.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise625/inj_proj_apply_le.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise625/inj_sSup.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise625/inj_sSup.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise625/lowerSet.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise625/lowerSet.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise625/lowerSet_bounded.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise625/lowerSet_bounded.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise625/lowerSet_directed.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise625/lowerSet_directed.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise625/mem_lowerSet.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise625/mem_lowerSet.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise625/proj_eq_sSup.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise625/proj_eq_sSup.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise625/proj_inj_apply.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise625/proj_inj_apply.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise625/upperSet.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise625/upperSet.lean)
- [NeighbourhoodSystems/DomainEquations/Exercise625/upperSet_nonempty.lean](DomainTheory/NeighbourhoodSystems/DomainEquations/Exercise625/upperSet_nonempty.lean)
