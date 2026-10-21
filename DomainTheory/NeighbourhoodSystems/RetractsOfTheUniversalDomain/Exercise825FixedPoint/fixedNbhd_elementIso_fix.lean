/-ai
For any finitary projection of the universal domain, the fixed neighbourhood of the projection is order-isomorphic to its fixed set. The isomorphism is the element isomorphism of the fixed-neighbourhood subsystem, after unfolding the retraction of that subsystem and rewriting it by the identity that the injection composed with the projection of a finitary projection is the projection itself.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Pow
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Embed
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Closing
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise820

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.NeighborhoodSystemu2eIsEffectivelyGivenu2etoS
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashMap_isComputable
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashProju2080_isComputable
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashProju2081_isComputable
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

/-- **`fixedNbhd a ≅ Fix(a)`, for any finitary projection `a : 𝒰 → 𝒰`.** Theorem 8.6(a)'s
`inj_comp_proj_eq_self` identifies `retractionOfSubsystem (fixedNbhd_subsystem a)` with `a` itself,
transporting Proposition 8.2's `elementIso` along the identification. -/
noncomputable def fixedNbhd_elementIso_fix {a : ApproximableMap U U} (ha : IsFinitaryProjection a) :
    (fixedNbhd a).Element ≃o {y : U.Element // a.toElementMap y = y} := by
  have h := Subsystem.elementIso (fixedNbhd_subsystem a)
  unfold Subsystem.retractionOfSubsystem at h
  rwa [inj_comp_proj_eq_self ha] at h

end DomainTheory.NeighbourhoodSystems
