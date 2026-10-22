module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.ComputablePresentation

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*}

/-- **Definition 7.1 (Scott 1981, PRG-19) — effectively given.** A neighbourhood system is
*effectively given* when it admits a computable presentation. -/
def NeighborhoodSystem.IsEffectivelyGiven (V : NeighborhoodSystem α) : Prop :=
  Nonempty (ComputablePresentation V)

end DomainTheory.NeighbourhoodSystems
