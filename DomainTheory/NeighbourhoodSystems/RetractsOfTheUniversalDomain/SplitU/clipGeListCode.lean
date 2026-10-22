module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.clipGeCode

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- Clip every pair of the list-code `c` into `[decodeRat m, ∞)`. -/
def clipGeListCode (m c : ℕ) : ℕ := flatMapCode (fun t => Nat.pair (clipGeCode t) 0 + 1) m c

end DomainTheory.NeighbourhoodSystems
