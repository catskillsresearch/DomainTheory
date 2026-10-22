# Exercise 7.19

**EXERCISE 7.19.** Prove that $D \mapsto \mathbb{P} D$ is a functor by defining for each $f : D \to E$ a mapping

$$\mathbb{P} f : \mathbb{P} D \to \mathbb{P} E$$

by the formula

$$\bigcup_{i < n} \downarrow X_i \quad \mathbb{P} f \quad \bigcup_{j < m} \downarrow Y_j \quad \text{iff} \quad \forall i < n \exists j < m.\, X_i f Y_j \, .$$

Be sure to check that $\mathbb{P} f$ is approximable and that $\mathbb{P}$ preserves identity maps and composition. If $f$ is computable, is $\mathbb{P} f$? Is there a combinator $\lambda f.\, \mathbb{P} f$? What is

$$\mathbb{P} f(\{x, y\}) = ??$$

**Lean 4**

- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/PDmem_down.lean](PDmem_down.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/PFmap.lean](PFmap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/PFmap_rel.lean](PFmap_rel.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/PFmapComb.lean](PFmapComb.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/Basic.lean](Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/PDmem_mem.lean](PDmem_mem.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/PFmap_idMap.lean](PFmap_idMap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/PFmap_rel_Ypd_iff.lean](PFmap_rel_Ypd_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/PFmap_rel_fin.lean](PFmap_rel_fin.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/bExists_decodeList_re.lean](bExists_decodeList_re.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/PFmap_isComputable_Ypd.lean](PFmap_isComputable_Ypd.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/PFmap_isComputable.lean](PFmap_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/comp_witness.lean](comp_witness.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/PFmap_comp.lean](PFmap_comp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/gather_witnesses.lean](gather_witnesses.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/exists_stepFun_forall_PFmap_rel.lean](exists_stepFun_forall_PFmap_rel.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719/PFmapComb_toElementMap.lean](PFmapComb_toElementMap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise719.lean](../Exercise719.lean)
