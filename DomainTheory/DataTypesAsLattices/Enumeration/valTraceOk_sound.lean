/-ai
If a valuation trace is well formed, then every entry of the trace has its member in the numerical value of its code.

The proof is by strong induction on the code. Structural well-formedness justifies the entry. At zero, the G clause and the zero law for the evaluator give membership in the G combinator. At a successor, the zero-code alternative of the justification is impossible. The remaining alternative, after the predecessor and unpairing identities, gives an operator membership of the pair of the time stamp with the member and witnesses for the set bits of the time stamp. Both unpairing components are strictly smaller, so the inductive hypothesis places the pair in the operator value and each set bit in the argument value. Membership of the member in the application of those two values rewrites, by the successor law, as membership at the successor code.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.unpairComp_eq

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem valTraceOk_sound {tr : ValTrace} (hok : valTraceOk tr) :
    ∀ {code member t}, (code, member, t) ∈ tr → member ∈ valNat code := by
  intro code member t hmem
  induction code using Nat.strongRecOn generalizing member t with
  | ind code ih =>
    have hjust := hok.1 (code, member, t) hmem
    cases code with
    | zero =>
      exact valNat_zero.symm ▸ hok.2 (0, member, t) hmem rfl
    | succ p =>
      rcases hjust with h0 | ⟨hop, hbits⟩
      · exact (Nat.succ_ne_zero p h0).elim
      · simp only [Nat.pred_succ, unpairComp_eq] at hop hbits
        have hop' : (unpair p).1 < p + 1 :=
          (pair_lt_left (unpair p).1 (unpair p).2).trans_le (by
            have := pair_unpair p
            omega)
        have harg : (unpair p).2 < p + 1 :=
          (pair_lt_right (unpair p).1 (unpair p).2).trans_le (by
            have := pair_unpair p
            omega)
        obtain ⟨tOp, htOp⟩ := hop
        have hopMem : pair t member ∈ valNat (unpair p).1 :=
          ih _ hop' htOp
        have hargMem : e t ⊆ valNat (unpair p).2 := by
          intro i hi
          have hlt : i < t + 1 := Nat.lt_succ_of_le (mem_e_le hi)
          have hbit : t.testBit i = true := mem_e.mp hi
          have hhas := (hbits i hlt).resolve_left fun hf => by
            simp [hbit] at hf
          obtain ⟨ti, hti⟩ := hhas
          exact ih _ harg hti
        have : member ∈ valNat (unpair p).1 ⬝ valNat (unpair p).2 :=
          ⟨t, hargMem, hopMem⟩
        exact valNat_succ p ▸ this

end DomainTheory.DataTypesAsLattices
