/-ai
The left endpoint of the first pair of the canonical presenting list is strictly less than the decoded midpoint.

Unfold the midpoint code and rewrite its decoding as the average of the two endpoints. The first pair is nondegenerate, so its left endpoint lies strictly below that average.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.splitU_p0_lt

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem


theorem splitU_mid_gt (n : ℕ) :
    (decodeRatPair (firstElemCode (canonCode n))).1 < decodeRat (splitMidCode n) := by
  show decodeRat (firstElemCode (canonCode n)).unpair.1 < decodeRat (splitMidCode n)
  unfold splitMidCode
  rw [decodeRat_ratMidCode']
  have h := splitU_p0_lt n
  unfold decodeRatPair at h
  exact left_lt_add_div_two.mpr h

end DomainTheory.NeighbourhoodSystems
