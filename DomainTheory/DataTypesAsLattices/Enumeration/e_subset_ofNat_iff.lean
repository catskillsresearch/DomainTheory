/-ai
The enumeration element of a code is contained in the numeral n if and only if the code is 0 or the code is 2 raised to the power n.

If the inclusion holds and the code is 0, that disjunct is immediate. Otherwise every set bit index equals n, because such an index lies in the numeral. The bit at the binary logarithm is set, so the bit at n is set. Comparing test bits, the bit at n agrees with the power of two, and every other bit of the code is unset, because a set bit at a different index would have to equal n. Conversely, if the code is 0 then membership in its enumeration simplifies by the empty enumeration of 0, and if the code is 2 to the power n then membership simplifies by the singleton enumeration of that power and the definition of a numeral.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code











theorem e_subset_ofNat_iff (code n : ℕ) :
    e code ⊆ ofNat n ↔ code = 0 ∨ code = 2 ^ n := by
  constructor
  · intro h
    by_cases hz : code = 0
    · exact Or.inl hz
    · have hbit : ∀ k, code.testBit k = true → k = n := by
        intro k hk
        simpa [ofNat] using h (mem_e.mpr hk)
      have hn : code.testBit n = true := by
        have hk : code.testBit code.log2 = true := Nat.testBit_log2 hz
        simpa [hbit _ hk] using hk
      refine Or.inr (Nat.eq_of_testBit_eq fun k => ?_)
      by_cases hk : k = n
      · subst hk
        simp [hn]
      · have hfalse : code.testBit k = false :=
          Bool.eq_false_iff.mpr fun hb => hk (hbit k hb)
        simp [hfalse, Ne.symm hk]
  · intro h
    rcases h with rfl | rfl
    · intro k hk
      simp [e_zero] at hk
    · intro k hk
      simpa [e_pow2, ofNat] using hk

end DomainTheory.DataTypesAsLattices
