/-ai
The finite set coded by n is contained in the finite set coded by b if and only if, for every k < n, bit k of n is unset or bit k of b is set.

If the inclusion holds and bit k of n is set, then k lies in the finite set coded by b, so that bit of b is set; if the bit of n is unset, that is the other disjunct. Conversely, an element k of the finite set coded by n lies strictly below n and has its bit set in n, so the hypothesis forces the bit in b.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic

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
