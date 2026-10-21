# Theorem 7.6

We have nearly all our favourite combinators computable, but perhaps the most important one - since it is the key to recursive definitions - is the fixed-point combinator. It is not left out.

**THEOREM 7.6.** For any effectively given domain $\mathcal{D}$, the combinator $\mathrm{fix} : (\mathcal{D} \to \mathcal{D}) \to \mathcal{D}$ is computable.

*Proof :* Referring back to the proof of Theorem 4.2 and thinking of

$$\mathcal{D} = \{ X_n \mid n \in \mathbb{N} \}$$

as effectively given, fix as a relation comes down to
$$\bigcap_{i < q} [X_{n_i}, X_{m_i}] \text{ fix } X_\ell \text{ iff for some finite sequence}$$

$$\Delta = X_{k_0}, \ldots, X_{k_p} = X_\ell,$$

we have, for each $j < p$,

$$\bigcap \{ X_{m_i} \mid X_{k_j} \subseteq X_{n_i} \} \subseteq X_{k_{j+1}}.$$

Inside the “for some finite sequence” all the checks are decidable by assumption on $D$. But the existential quantification of a decidable predicate always gives a recursively enumerable predicate. (And, as there is no implied bound on the size of the finite sequence we are looking for, this really *is* an enumerable set and not generally a recursive set.) $\square$

**Lean 4**

- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/Basic.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/Basic.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/Xenum_codePair.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/Xenum_codePair.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/chainDec.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/chainDec.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/chainDec_iff_gStepsOK.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/chainDec_iff_gStepsOK.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/codePair.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/codePair.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/fixChainChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/fixChainChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/fixChainChar_eq.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/fixChainChar_eq.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/fixChainChar_spec.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/fixChainChar_spec.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/fixElement_mem_iff_chain.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/fixElement_mem_iff_chain.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/fixMap_isComputable.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/fixMap_isComputable.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/fixMap_rel_iff.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/fixMap_rel_iff.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/fixPStep.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/fixPStep.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/fixPStep_foldl_fst.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/fixPStep_foldl_fst.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/fixPStep_foldl_snd.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/fixPStep_foldl_snd.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/fixStp.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/fixStp.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/fixStp_eq.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/fixStp_eq.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/gLastOf.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/gLastOf.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/gStepsOK.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/gStepsOK.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/gStepsOK_complete.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/gStepsOK_complete.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/gStepsOK_sound.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/gStepsOK_sound.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/leastMap_Xenum_rel.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/leastMap_Xenum_rel.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/primrec_fixChainChar.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/primrec_fixChainChar.lean)
- [NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/primrec_fixStp.lean](DomainTheory/NeighbourhoodSystems/ComputabilityInEffectivelyGivenDomains/Theorem76/primrec_fixStp.lean)
