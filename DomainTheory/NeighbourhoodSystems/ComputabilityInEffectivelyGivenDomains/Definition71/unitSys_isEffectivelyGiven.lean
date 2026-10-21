/-ai
The one-point neighbourhood system is effectively given.

The trivial presentation is a computable presentation of it.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*}


/-- **The one-point domain `𝟙` is effectively given.** -/
theorem unitSys_isEffectivelyGiven : unitSys.IsEffectivelyGiven :=
  ⟨unitPresentation⟩

end DomainTheory.NeighbourhoodSystems
