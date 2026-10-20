module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.decodeInt_encodeInt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.decodeRat_encodeRat
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.ratLeCode

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- `ratLtCode (pair c₁ c₂)` decides `decodeRat c₁ < decodeRat c₂` via `¬ (decodeRat c₂ ≤ decodeRat c₁)`. -/
def ratLtCode (t : ℕ) : ℕ := 1 - ratLeCode (Nat.pair t.unpair.2 t.unpair.1)

end DomainTheory.NeighbourhoodSystems
