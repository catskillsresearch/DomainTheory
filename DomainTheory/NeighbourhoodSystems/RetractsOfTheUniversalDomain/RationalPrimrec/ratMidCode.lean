module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.decodeInt_encodeInt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.decodeRat_encodeRat
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.qNumP
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.qNumN
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.qDen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.decodeRat_zeroCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.decodeRat_oneCode

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- The midpoint code `(c₁+c₂)/2` of two rational codes, via denominator cross-clearing (as in
`ratLeCode`) for the sum, then doubling the denominator to halve. -/
def ratMidCode (t : ℕ) : ℕ :=
  let c1 := t.unpair.1; let c2 := t.unpair.2
  Nat.pair (Nat.pair (qNumP c1 * qDen c2 + qNumP c2 * qDen c1)
                      (qNumN c1 * qDen c2 + qNumN c2 * qDen c1))
    (2 * qDen c1 * qDen c2 - 1)

end DomainTheory.NeighbourhoodSystems
