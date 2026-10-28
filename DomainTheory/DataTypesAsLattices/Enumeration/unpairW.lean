
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Enumeration.unpairWRec
public import DomainTheory.DataTypesAsLattices.Enumeration.exists_triangle_succ
public import DomainTheory.DataTypesAsLattices.Pomega.pair

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def unpairW (k : ℕ) : ℕ := unpairWRec k k

namespace unpairW

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem eq (k : ℕ) : unpairW k = Nat.find (exists_triangle_succ k) := by
  refine ((Nat.find_eq_iff (exists_triangle_succ k)).mpr ⟨?_, fun m hm =>
      unpairWRec.min k k m hm⟩).symm
  rcases unpairWRec.lt k k with h | hrec
  · exact h
  · have : k + 1 ≤ triangle (k + 1) := by
      cases k with
      | zero => simp [triangle]
      | succ k =>
        rw [triangle_succ]
        exact Nat.le_add_left _ _
    simpa [unpairW, hrec] using lt_of_lt_of_le (Nat.lt_succ_self k) this

end unpairW

end DomainTheory.DataTypesAsLattices
