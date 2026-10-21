/-ai
Encoding a pair of rationals as a natural number is the natural pairing of the two rational encodings.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- Encode a pair of rationals as a single natural. -/
def encodeRatPair (p : ℚ × ℚ) : ℕ := Nat.pair (encodeRat p.1) (encodeRat p.2)

end DomainTheory.NeighbourhoodSystems
