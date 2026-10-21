/-ai
The powerset domain is effectively given.

The computable presentation of the powerset is a witness.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example78

open Domain.Recursive NeighborhoodSystem








/-- **Example 7.8 (Scott 1981, PRG-19).** The powerset domain `PN` is effectively given. -/
theorem PN_isEffectivelyGiven : PN.IsEffectivelyGiven := ⟨PNpres⟩

end DomainTheory.NeighbourhoodSystems.Example78
