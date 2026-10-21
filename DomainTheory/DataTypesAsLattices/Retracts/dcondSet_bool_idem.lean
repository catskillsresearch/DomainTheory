/-ai
The doubly strict conditional on the numerals zero and one is idempotent. A second pass leaves the Boolean value unchanged, and mixed tags stay collapsed.

The proof splits into the four cases of the conditional on the test: zero without a positive element, a positive element without zero, a mixed set, and the empty set. In each case the matching evaluation rewrites the inner conditional and then the outer one, and the two sides agree.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


































































/-- `bool` is idempotent: mixed tags collapse to `⊤`, a fixed point of `⊒`. -/
theorem dcondSet_bool_idem (u : Pomega) :
    dcondSet (dcondSet u (ofNat 0) (ofNat 1)) (ofNat 0) (ofNat 1) =
      dcondSet u (ofNat 0) (ofNat 1) := by
  rcases dcondSet_cases u with h | h | h | h
  · rw [dcondSet_of_zero_not_pos h.1 h.2, dcondSet_ofNat_zero]
  · rw [dcondSet_of_pos_not_zero h.1 h.2, dcondSet_ofNat_one]
  · rw [dcondSet_of_mixed h.1 h.2, dcondSet_top]
  · rw [dcondSet_of_empty h.1 h.2, dcondSet_bot]

end DomainTheory.DataTypesAsLattices
