# Theorem 8.6

The criterion for being a finitary projection just obtained provides us with a very interesting new combinator.

**THEOREM 8.6.** For any domain $E$ define

$$\mathrm{sub} : (E \to E) \to (E \to E)$$

by the formula

$$X \ \mathrm{sub} \ (f) \ Z \quad \text{iff} \quad \exists Y \in E.\quad X \subseteq Y \ \ f \ Y \subseteq Z,$$
for all $X, Z \in E$ and all $f : E \to E$. Then the range of $\mathrm{sub}$ consists exactly of the finitary projections on $E$, and moreover $\mathrm{sub}$ itself is a finitary projection on $(E \to E)$. If $E$ is effectively given, then $\mathrm{sub}$ is computable.

*Proof:* It is trivial to check that $\mathrm{sub}(f)$ is always approximable. Also, it is obvious from the definition that the correspondence

$$f \mapsto \mathrm{sub}(f)$$

preserves directed unions of $f$'s. Thus, $\mathrm{sub}$ is itself approximable. We note that

$$X \subseteq Y \ \ f \ Y \subseteq Z \text{ always implies } X \ f \ Z;$$

hence, $\mathrm{sub}(f) \subseteq f$ holds. Also

$$Y \ f \ Y \text{ always implies } Y \ \mathrm{sub}(f) \ Y,$$

hence, $\mathrm{sub}(f) \subseteq \mathrm{sub}(\mathrm{sub}(f))$ holds. This shows $\mathrm{sub}$ to be a projection on $(E \to E)$. The effectiveness of the definition makes it also clear that $\mathrm{sub}$ is computable when $E$ has a computable presentation.

Since, $\mathrm{sub}$ is a projection, its range is the same as its fixed-point set. If

$$\mathrm{sub}(a) = a,$$

then there is no problem in checking that $a$ satisfies 8.5(ii) *and conversely*. So the range of $\mathrm{sub}$ picks out exactly the finitary projections in view of 8.5.

Finally, to prove that $\mathrm{sub}$ is a finitary projection of $(E \to E)$, we invoke 6.11 and remark that, in view of 8.2, the fixed point set (range) of $\mathrm{sub}$ is in a one-one inclusion-preserving correspondence with the domain $\{D \mid D \triangleleft E\}$. $\square$

**Lean 4**

- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/Basic.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/continuous_subFilter.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/continuous_subFilter.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/finitaryProjectionSubsystemEquiv.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/finitaryProjectionSubsystemEquiv.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/fixedNbhd_retractionOfSubsystem.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/fixedNbhd_retractionOfSubsystem.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/fixedNbhd_sub.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/fixedNbhd_sub.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/isFinitaryProjection_of_sub_eq_self.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/isFinitaryProjection_of_sub_eq_self.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/isFinitaryProjection_sub.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/isFinitaryProjection_sub.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/isFinitaryProjection_subApprox.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/isFinitaryProjection_subApprox.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/isProjection_subApprox.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/isProjection_subApprox.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/isRetraction_subApprox.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/isRetraction_subApprox.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/sub.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/sub.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/subApprox.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/subApprox.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/subApproxFixIso.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/subApproxFixIso.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/subApprox_le_idMap.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/subApprox_le_idMap.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/subFilter.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/subFilter.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/subFilter_iSupDirected.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/subFilter_iSupDirected.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/subFilter_mono.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/subFilter_mono.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/subFilter_monotone.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/subFilter_monotone.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/subFilter_subFilter.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/subFilter_subFilter.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/sub_eq_self_iff_isFinitaryProjection.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/sub_eq_self_iff_isFinitaryProjection.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/sub_eq_self_of_isFinitaryProjection.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/sub_eq_self_of_isFinitaryProjection.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/sub_le.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/sub_le.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/sub_mono.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/sub_mono.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/sub_rel.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/sub_rel.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/sub_retractionOfSubsystem.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/sub_retractionOfSubsystem.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/sub_sub.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/sub_sub.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/sub_toApproxMap_iSupDirected.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/sub_toApproxMap_iSupDirected.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/toApproxMap_injective.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/toApproxMap_injective.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/toApproxMap_monotone.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/toApproxMap_monotone.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/toApproxMap_rel_iSupDirected.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/toApproxMap_rel_iSupDirected.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/toApproxMap_subFilter.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/toApproxMap_subFilter.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/toApproxMap_toFilter.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/toApproxMap_toFilter.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/toElementMap_subApprox.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/toElementMap_subApprox.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/toElementMap_subApprox_comp.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/toElementMap_subApprox_comp.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/toFilter_toApproxMap.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86/toFilter_toApproxMap.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86c.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86c.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86c/Basic.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86c/Basic.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86c/subApprox_isComputable.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86c/subApprox_isComputable.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86c/subApprox_rel_Xenum_iff.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86c/subApprox_rel_Xenum_iff.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86c/subApprox_rel_iff.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86c/subApprox_rel_iff.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86c/subStep_recDecidable.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86c/subStep_recDecidable.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86c/sub_isComputable_of_isEffectivelyGiven.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86c/sub_isComputable_of_isEffectivelyGiven.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86c/sub_leastMap_rel_iff.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86c/sub_leastMap_rel_iff.lean)
- [NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86c/sub_rel_iff_exists_index.lean](DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/Theorem86c/sub_rel_iff_exists_index.lean)
