module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.ComputablePresentation

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*}

namespace ComputablePresentation

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)

/-- Swap the two components of a `Nat.pair` code: `t ↦ pair m n`. -/
def swapPair (t : ℕ) : ℕ := Nat.pair t.unpair.2 t.unpair.1

end ComputablePresentation

end DomainTheory.NeighbourhoodSystems
