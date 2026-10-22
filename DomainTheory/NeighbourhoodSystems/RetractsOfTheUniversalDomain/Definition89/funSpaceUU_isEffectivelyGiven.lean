module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.U_isEffectivelyGiven
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

/-- `𝒰 → 𝒰` is effectively given (Theorem 7.5, applied to `U`'s own presentation twice). -/
theorem funSpaceUU_isEffectivelyGiven : (funSpace U U).IsEffectivelyGiven :=
  funSpace_isEffectivelyGiven U_isEffectivelyGiven U_isEffectivelyGiven

end DomainTheory.NeighbourhoodSystems
