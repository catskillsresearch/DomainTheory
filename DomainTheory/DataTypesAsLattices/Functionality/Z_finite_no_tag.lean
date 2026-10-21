/-ai
The pair of one more than the maximum of p and q with any code does not belong to the m-fold iterator of the finite set coded by p started at the finite set coded by q.

A supposed membership is bounded by the finite bound. The inequality for the left component of a pair then makes the successor of the maximum less than or equal to the maximum, which is impossible.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.Z_finite_bound

@[expose] public section


namespace DomainTheory.DataTypesAsLattices



























theorem Z_finite_no_tag (p q m k : ℕ) :
    pair (max p q + 1) k ∉ Z m (e p) (e q) := by
  intro hk
  have hle := Z_finite_bound p q m _ hk
  exact (Nat.not_succ_le_self (max p q))
    ((pair_le_left (max p q + 1) k).trans hle)

end DomainTheory.DataTypesAsLattices
