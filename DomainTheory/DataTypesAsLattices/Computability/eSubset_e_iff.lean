module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Pomega.e

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem eSubset_e_iff (n b : ℕ) :
    e n ⊆ e b ↔ ∀ k < n, n.testBit k = false ∨ b.testBit k = true := by
  constructor
  · intro h k hk
    by_cases hb : n.testBit k = true
    · exact Or.inr (mem_e.mp (h (mem_e.mpr hb)))
    · exact Or.inl (Bool.eq_false_iff.mpr hb)
  · intro h k hk
    have hlt : k < n := mem_e_lt hk
    exact mem_e.mpr ((h k hlt).resolve_left fun hf =>
      Bool.eq_false_iff.mp hf (mem_e.mp hk))

end DomainTheory.DataTypesAsLattices
