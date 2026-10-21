# Exercise 7.17

**EXERCISE 7.17.** Complete the proof of 7.7 for showing that $D^{\S}$ is effectively given if $D$ is. Include all the combinators of 6.2. Prove also that if $E$ is effectively given and $u : D \to E$ and $v : E \times E \to E$ are computable, then the unique strict mapping $g : D^{\S} \to E$, where, for $x \in |D|$ and $y, z \in |E|$,

$$g(\mathrm{in}(x)) = u(x), \quad \text{and}$$

$$g(\mathrm{pair}(y, z)) = v(g(y), g(z)),$$

is a computable mapping.

**Lean 4**

- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717.lean](../Exercise717.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717/Basic.lean](../Exercise717/Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717/pairSharpMap.lean](../Exercise717/pairSharpMap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717/pairSharpMap_toElementMap.lean](../Exercise717/pairSharpMap_toElementMap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717/pairSharp_isComputable.lean](../Exercise717/pairSharp_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717/pairSharp_rel_Vsharp_iff.lean](../Exercise717/pairSharp_rel_Vsharp_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717/proj1Map.lean](../Exercise717/proj1Map.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717/proj1Map_rel.lean](../Exercise717/proj1Map_rel.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717/proj1_isComputable.lean](../Exercise717/proj1_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717/proj1_rel_Vsharp_iff.lean](../Exercise717/proj1_rel_Vsharp_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717/proj1_toElementMap_pairSharp.lean](../Exercise717/proj1_toElementMap_pairSharp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2.lean](../Exercise717Part2.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/Basic.lean](Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/GRel.lean](GRel.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/embZero_ne_embPair_of_memS.lean](embZero_ne_embPair_of_memS.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gEval.lean](gEval.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gEval_complete.lean](gEval_complete.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gEval_out.lean](gEval_out.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gEval_pair.lean](gEval_pair.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gEval_sound.lean](gEval_sound.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gMap.lean](gMap.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gMap_in.lean](gMap_in.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gMap_isComputable.lean](gMap_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gMap_pair.lean](gMap_pair.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gMap_rel.lean](gMap_rel.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gMap_strict.lean](gMap_strict.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gRel_cod.lean](gRel_cod.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gRel_dom.lean](gRel_dom.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gRel_embPair_inv.lean](gRel_embPair_inv.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gRel_embZero_inv.lean](gRel_embZero_inv.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gRel_gamma_inv.lean](gRel_gamma_inv.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gRel_interRight.lean](gRel_interRight.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gRel_master.lean](gRel_master.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gRel_mono.lean](gRel_mono.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gStep.lean](gStep.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gStep_gamma.lean](gStep_gamma.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gStep_leaf.lean](gStep_leaf.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/gStep_node.lean](gStep_node.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/listGet_rtbl_gEval.lean](listGet_rtbl_gEval.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/pair_le_pair_right.lean](pair_le_pair_right.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/pair_lt_pair_left.lean](pair_lt_pair_left.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/pair_lt_pair_of_lt_le.lean](pair_lt_pair_of_lt_le.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/primrec_gStep.lean](primrec_gStep.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/unpair_snd_snd_fst_le.lean](unpair_snd_snd_fst_le.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Exercise717Part2/unpair_snd_snd_snd_le.lean](unpair_snd_snd_snd_le.lean)
