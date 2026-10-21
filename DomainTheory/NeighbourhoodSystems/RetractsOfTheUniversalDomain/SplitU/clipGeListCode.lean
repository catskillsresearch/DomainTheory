/-ai
clipGeListCode m c clips every rational pair in the list code c into the closed ray from the rational decoded by m. It flat-maps the list with m held fixed, sending each pair code to the singleton list code of its clip.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.clipGeCode

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- Clip every pair of the list-code `c` into `[decodeRat m, ∞)`. -/
def clipGeListCode (m c : ℕ) : ℕ := flatMapCode (fun t => Nat.pair (clipGeCode t) 0 + 1) m c

end DomainTheory.NeighbourhoodSystems
