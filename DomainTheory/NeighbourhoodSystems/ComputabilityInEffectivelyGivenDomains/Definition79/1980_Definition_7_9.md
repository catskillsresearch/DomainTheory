# Definition 7.9

**DEFINITION 7.9.** Let $\mathcal{D}$ be any neighbourhood system and define

$$\mathbb{P}\mathcal{D} = \left\{ \bigcup_{i < n} (\downarrow X_i) \mid \forall i < n.\, X_i \in \mathcal{D} \right\}.$$

We recall that for any $X \in \mathcal{D}$

$$\downarrow X = \{ Y \in \mathcal{D} \mid Y \subseteq X \}.$$

The finite unions in $\mathbb{P}\mathcal{D}$ can be empty (i.e. if $n = 0$). $\square$

Formally, the system $\mathbb{P}\mathcal{D}$ is just more or less the closure of $\mathcal{D}$ under finite unions; however, this would not be an isomorphism-invariant construct unless $\mathcal{D}$ is "prepared". The preparation consists of replacing $\mathcal{D}$ by the isomorphic domain

$$\mathcal{D}^\dagger = \{ \downarrow X \mid X \in \mathcal{D} \}.$$

(In this connection refer back to Exercise 1.20.) We remark that

$$\downarrow X \cap \downarrow Y \neq \emptyset \text{ iff } \{X, Y\} \text{ is consistent in } \mathcal{D},$$

and in that case

$$\downarrow X \cap \downarrow Y = \downarrow (X \cap Y).$$

**Lean 4**

- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79/Basic.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79/Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79/PDmem.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79/PDmem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79/PDmem_empty.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79/PDmem_empty.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79/PDmem_iff_fin.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79/PDmem_iff_fin.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79/PDmem_master.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79/PDmem_master.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79/PDmem_union.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79/PDmem_union.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79/PDmem_upSet.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79/PDmem_upSet.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79/dagger_isomorphic.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79/dagger_isomorphic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79/dagger_upSet_inter.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79/dagger_upSet_inter.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79/mem_PDunion.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79/mem_PDunion.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79/upSet_inter_nonempty_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Definition79/upSet_inter_nonempty_iff.lean)
