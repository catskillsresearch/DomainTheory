# Exercise 7.20

**EXERCISE 7.20.** Show that there is a combinator

$$\text{union} : \mathbb{P}(\mathbb{P} D) \to \mathbb{P} D$$

where for suitable neighbourhoods

$$\bigcup_{i < n} \downarrow \Bigl(\bigcup_{j < m_i} \downarrow X_{ij}\Bigr) \quad \text{union} \quad \bigcup_{k < q} \downarrow Y_k \quad \text{iff} \quad \forall i < n \forall j < m_i \exists k < q.\, X_{ij} \subseteq Y_k \, .$$

Is union computable if $D$ is effectively given? What is

$$\text{union}(\{\{x\}, \{y, z\}\}) = ??$$

Are $\mathbb{P}(\mathbb{P} D)$ and $\mathbb{P} D$ generally isomorphic??

**Lean 4**

- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise720.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise720.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise720/Basic.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise720/Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise720/unionMap.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise720/unionMap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise720/unionMap_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise720/unionMap_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise720/unionMap_rel_Ypd_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise720/unionMap_rel_Ypd_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise720/unionMap_rel_fin.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise720/unionMap_rel_fin.lean)
