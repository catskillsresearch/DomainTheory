module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem


/-- **Exercise 8.12(b) (Scott 1981, PRG-19).** `V` is effectively given. -/
theorem V_isEffectivelyGiven : V.IsEffectivelyGiven := ⟨VComputablePresentation⟩

end DomainTheory.NeighbourhoodSystems
