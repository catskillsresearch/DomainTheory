# Exercise 3.19

**EXERCISE 3.19.** Suppose we are given systems and approximable mappings

$$
f : \mathcal{D}_0 \to \mathcal{D}'_0 \quad \text{and} \quad g : \mathcal{D}_1 \to \mathcal{D}'_1.
$$

Prove there are approximable mappings

$$
f \times g : \mathcal{D}_0 \times \mathcal{D}_1 \to \mathcal{D}'_0 \times \mathcal{D}'_1 \quad \text{and} \quad f + g : \mathcal{D}_0 + \mathcal{D}_1 \to \mathcal{D}'_0 + \mathcal{D}'_1
$$

such that

(i) $(f \times g)(x, y) = \langle f(x), g(y) \rangle$ for all $x \in |\mathcal{D}_0|$ and $y \in |\mathcal{D}_1|$, and rewrite this as:

(ii) $f \times g = \langle f \circ p_0, g \circ p_1 \rangle$.

In addition prove that

(iii) $out_0 \circ (f + g) \circ in_0 = f$, and

(iv) $out_1 \circ (f + g) \circ in_1 = g$.

Do equations (iii) and (iv) uniquely determine $f + g$?

**Lean 4**

- [NeighbourhoodSystems/DomainConstructs/Exercise319.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise319.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise319/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise319/Basic.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise319/paired_unique.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise319/paired_unique.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise319/prodMap.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise319/prodMap.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise319/prodMap_comp.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise319/prodMap_comp.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise319/prodMap_id.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise319/prodMap_id.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise319/proj_paired.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise319/proj_paired.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise319/toElementMap_prodMap.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise319/toElementMap_prodMap.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise319/toElementMap_prodMap_pair.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise319/toElementMap_prodMap_pair.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise319Sum.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise319Sum.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise319Sum/Basic.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise319Sum/Basic.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise319Sum/eq_sumMaster_of_subset.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise319Sum/eq_sumMaster_of_subset.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise319Sum/mem_subset_inj₀.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise319Sum/mem_subset_inj₀.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise319Sum/mem_subset_inj₁.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise319Sum/mem_subset_inj₁.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise319Sum/not_inj₀_subset_inj₁.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise319Sum/not_inj₀_subset_inj₁.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise319Sum/not_inj₁_subset_inj₀.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise319Sum/not_inj₁_subset_inj₀.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise319Sum/outMapu2080_comp_sumMap_comp_inMapu2080.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise319Sum/outMapu2080_comp_sumMap_comp_inMapu2080.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise319Sum/outMapu2081_comp_sumMap_comp_inMapu2081.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise319Sum/outMapu2081_comp_sumMap_comp_inMapu2081.lean)
- [NeighbourhoodSystems/DomainConstructs/Exercise319Sum/sumMap.lean](DomainTheory/NeighbourhoodSystems/DomainConstructs/Exercise319Sum/sumMap.lean)
