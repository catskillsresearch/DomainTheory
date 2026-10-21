/-ai
Decoding a natural number as a rational pair is the pair of the rational decodings of its two unpaired components.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- Decode a natural as a pair of rationals. -/
def decodeRatPair (c : ℕ) : ℚ × ℚ := (decodeRat c.unpair.1, decodeRat c.unpair.2)

end DomainTheory.NeighbourhoodSystems
