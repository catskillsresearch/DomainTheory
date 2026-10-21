/-ai
A decoded rational equals the rational whose numerator is the difference of the positive and negative numerator parts of the code and whose denominator is the denominator of the code.

Unfolding the decoder, the integer decoder, and the three component maps makes the two sides identical.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.decodeInt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.decodeInt_encodeInt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.decodeRat
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.decodeRat_encodeRat
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.qNumP
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.qNumN
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.qDen

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

theorem decodeRat_eq (c : ℕ) :
    decodeRat c = mkRat ((qNumP c : ℤ) - (qNumN c : ℤ)) (qDen c) := by
  unfold decodeRat decodeInt qNumP qNumN qDen; rfl

end DomainTheory.NeighbourhoodSystems
