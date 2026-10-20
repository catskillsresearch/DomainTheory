module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem














































/-- **`𝒰` is effectively given.** -/
theorem U_isEffectivelyGiven : U.IsEffectivelyGiven := ⟨UComputablePresentation⟩

end DomainTheory.NeighbourhoodSystems
