module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Pomega.eDense

public import DomainTheory.DataTypesAsLattices.Graph.Basic.notation3
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
    · exact Or.inr (h (e.mem.mpr hb))
    · exact Or.inl (Bool.eq_false_iff.mpr hb)
  · intro h i hi
    have hlt : i < k := e.mem_lt hi
    exact (h i hlt).resolve_left fun hf =>
      Bool.eq_false_iff.mp hf (e.mem.mp hi)

end DomainTheory.DataTypesAsLattices
