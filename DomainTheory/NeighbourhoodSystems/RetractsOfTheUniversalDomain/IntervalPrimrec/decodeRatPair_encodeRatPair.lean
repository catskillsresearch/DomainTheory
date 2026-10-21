/-ai
Decoding the encoding of a rational pair returns that pair.

Unfold both sides and cancel unpairing together with rational encoding and decoding on each component.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.encodeRatPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.decodeRatPair

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

@[simp] theorem decodeRatPair_encodeRatPair (p : ℚ × ℚ) : decodeRatPair (encodeRatPair p) = p := by
  unfold decodeRatPair encodeRatPair
  simp only [unpair_pair_fst, unpair_pair_snd, decodeRat_encodeRat]

end DomainTheory.NeighbourhoodSystems
