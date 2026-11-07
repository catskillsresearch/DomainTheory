module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.powersetNbhd

@[expose] public section

open DomainTheory.NeighbourhoodSystems
open Domain.Recursive

/-- Scott's Example 7.8: the powerset of the naturals is effectively given. -/
theorem example_78 : PN.IsEffectivelyGiven :=
  PN_isEffectivelyGiven
