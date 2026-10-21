/-ai
An integer is encoded as the pair of the truncation of the integer and the truncation of its negation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- Encode an integer as the difference-pair `(z.toNat, (-z).toNat)` (one of the two is always
`0`). -/
def encodeInt (z : ℤ) : ℕ := Nat.pair z.toNat (-z).toNat

end DomainTheory.NeighbourhoodSystems
