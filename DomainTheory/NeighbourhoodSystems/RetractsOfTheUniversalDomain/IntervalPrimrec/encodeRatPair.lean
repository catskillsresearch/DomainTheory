module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- Encode a pair of rationals as a single natural. -/
def encodeRatPair (p : ℚ × ℚ) : ℕ := Nat.pair (encodeRat p.1) (encodeRat p.2)

end DomainTheory.NeighbourhoodSystems
