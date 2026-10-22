/-ai
The finite set coded by k is contained in the application of the finite sets coded by a and b if and only if, for every i < k, bit i of k is unset or i lies in that application.

If the inclusion holds and the bit is set, the element lies in the application; if the bit is unset, that is the other disjunct. Conversely, an element of the finite set coded by k lies strictly below k and has its bit set, so the hypothesis places it in the application.
ai-/
module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem eSubset_funOf_e_iff (k a b : ℕ) :
    e k ⊆ e a ⬝ e b ↔
      ∀ i < k, k.testBit i = false ∨ i ∈ e a ⬝ e b := by
  constructor
  · intro h i hi
    by_cases hb : k.testBit i = true
    · exact Or.inr (h (mem_e.mpr hb))
    · exact Or.inl (Bool.eq_false_iff.mpr hb)
  · intro h i hi
    have hlt : i < k := mem_e_lt hi
    exact (h i hlt).resolve_left fun hf =>
      Bool.eq_false_iff.mp hf (mem_e.mp hi)

end DomainTheory.DataTypesAsLattices
