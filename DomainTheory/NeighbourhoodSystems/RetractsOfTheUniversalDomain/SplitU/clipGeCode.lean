module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- Clip a rational-pair code `e` to `[decodeRat m, ∞)`, given `t = pair m e`. -/
def clipGeCode (t : ℕ) : ℕ :=
  Nat.pair (ratMaxCode (Nat.pair t.unpair.2.unpair.1 t.unpair.1)) t.unpair.2.unpair.2

end DomainTheory.NeighbourhoodSystems
