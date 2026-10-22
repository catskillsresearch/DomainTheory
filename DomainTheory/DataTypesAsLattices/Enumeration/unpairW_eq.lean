/-ai
The value unpairW k is the least natural number w such that k lies strictly below triangle (w + 1).

The least-number characterization asks for that triangle bound at unpairW k and for its failure at every smaller index. The failures are the minimality lemma for unpairWRec. The bound is the first alternative of unpairWRec_lt. In the other alternative, unpairWRec k k equals k. Then k + 1 is at most triangle (k + 1), by the definition of triangle at zero and by the successor equation for triangle together with the bound on a sum at a successor, so the inequality k < k + 1 yields k < triangle (k + 1). Rewriting by the definition of unpairW and by that alternative gives the required bound.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.unpairWRec_lt
public import DomainTheory.DataTypesAsLattices.Enumeration.unpairWRec_min

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem unpairW_eq (k : ℕ) : unpairW k = Nat.find (exists_triangle_succ k) := by
  refine ((Nat.find_eq_iff (exists_triangle_succ k)).mpr ⟨?_, fun m hm =>
      unpairWRec_min k k m hm⟩).symm
  rcases unpairWRec_lt k k with h | hrec
  · exact h
  · have : k + 1 ≤ triangle (k + 1) := by
      cases k with
      | zero => simp [triangle]
      | succ k =>
        rw [triangle_succ]
        exact Nat.le_add_left _ _
    simpa [unpairW, hrec] using lt_of_lt_of_le (Nat.lt_succ_self k) this

end DomainTheory.DataTypesAsLattices
