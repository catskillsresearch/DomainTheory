/-ai
The inclusion reindexing sends the pair code of indices n and m to the code of the triple n, m, n.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.ComputablePresentation

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*}

namespace ComputablePresentation

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)

/-- Reindexing `(n, m) ↦ (n, m, n)` on `Nat.pair` codes: `t ↦ pair n (pair m n)`. -/
def inclShuffle (t : ℕ) : ℕ := Nat.pair t.unpair.1 (Nat.pair t.unpair.2 t.unpair.1)

end ComputablePresentation

end DomainTheory.NeighbourhoodSystems
