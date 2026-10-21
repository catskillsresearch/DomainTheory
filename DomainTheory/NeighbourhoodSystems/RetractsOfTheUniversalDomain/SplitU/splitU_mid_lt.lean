/-ai
The decoded midpoint is strictly less than the right endpoint of the first pair of the canonical presenting list.

Unfold the midpoint code and rewrite its decoding as the average of the two endpoints. The first pair is nondegenerate, so that average lies strictly below the right endpoint.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.splitU_p0_lt

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

















theorem splitU_mid_lt (n : ℕ) :
    decodeRat (splitMidCode n) < (decodeRatPair (firstElemCode (canonCode n))).2 := by
  show decodeRat (splitMidCode n) < decodeRat (firstElemCode (canonCode n)).unpair.2
  unfold splitMidCode
  rw [decodeRat_ratMidCode']
  have h := splitU_p0_lt n
  unfold decodeRatPair at h
  exact add_div_two_lt_right.mpr h

end DomainTheory.NeighbourhoodSystems
