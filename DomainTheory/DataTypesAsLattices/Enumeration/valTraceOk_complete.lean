/-ai
If a member lies in the numerical value of a code, then some well-formed valuation trace records that code and that member.

The proof is by strong induction on the code. At zero, the zero clause of the evaluator places the member in the G combinator, and the one-entry trace with that member is well formed and records the membership. At a successor, both unpairing components are strictly smaller. The successor clause supplies a time stamp, an operator membership of the pair of that time stamp with the member, and a containment of the finite set of its set bits in the argument value. The inductive hypothesis gives a well-formed trace for the operator membership, and a concatenation of traces gives a well-formed trace recording each set bit of the time stamp at the argument code. Appending those traces preserves well-formedness and the recorded memberships. Consing the successor entry is justified by the transferred operator witness and bit witnesses, after the predecessor and unpairing identities, and the new code is a successor, so the extended trace is well formed and records the membership at that time stamp.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.unpairComp_eq
public import DomainTheory.DataTypesAsLattices.Enumeration.valTraceOk_zero
public import DomainTheory.DataTypesAsLattices.Enumeration.valTraceHas_append_left
public import DomainTheory.DataTypesAsLattices.Enumeration.valTraceHas_append_right
public import DomainTheory.DataTypesAsLattices.Enumeration.valTraceOk_append
public import DomainTheory.DataTypesAsLattices.Enumeration.valTraceOk_cons
public import DomainTheory.DataTypesAsLattices.Enumeration.exists_concat_traces

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem valTraceOk_complete :
    ∀ code member, member ∈ valNat code →
      ∃ tr, valTraceOk tr ∧ valTraceHas tr code member := by
  intro code
  induction code using Nat.strongRecOn with
  | ind code ih =>
    intro member hm
    cases code with
    | zero =>
      obtain ⟨hok0, hhas0⟩ := valTraceOk_zero member (valNat_zero ▸ hm)
      exact ⟨[(0, member, 0)], hok0, hhas0⟩
    | succ p =>
      have hop' : (unpair p).1 < p + 1 :=
        (pair_lt_left (unpair p).1 (unpair p).2).trans_le (by
          have := pair_unpair p
          omega)
      have harg : (unpair p).2 < p + 1 :=
        (pair_lt_right (unpair p).1 (unpair p).2).trans_le (by
          have := pair_unpair p
          omega)
      have hm' : member ∈ valNat (unpair p).1 ⬝ valNat (unpair p).2 :=
        valNat_succ p ▸ hm
      obtain ⟨t, htSub, htOp⟩ := hm'
      obtain ⟨trOp, hokOp, hhasOp⟩ := ih _ hop' _ htOp
      let bits := (List.range (t + 1)).filter (fun i => t.testBit i = true)
      obtain ⟨trBits, hokBits, hhasBits⟩ :=
        exists_concat_traces (c := (unpair p).2) bits fun i hi => by
          have : i ∈ e t := by
            have hmem : i ∈ List.range (t + 1) ∧ t.testBit i = true := by
              simpa [bits, List.mem_filter] using hi
            exact mem_e.mpr hmem.2
          exact ih _ harg i (htSub this)
      let trRest := trOp ++ trBits
      have hokRest : valTraceOk trRest := valTraceOk_append hokOp hokBits
      have hhasOp' : valTraceHas trRest (unpair p).1 (pair t member) :=
        valTraceHas_append_left hhasOp
      have hhasBits' : ∀ i < t + 1,
          t.testBit i = false ∨ valTraceHas trRest (unpair p).2 i := by
        intro i hi
        by_cases hb : t.testBit i = true
        · refine Or.inr (valTraceHas_append_right (hhasBits i ?_))
          simp [bits, List.mem_filter, List.mem_range, hi, hb]
        · exact Or.inl (Bool.eq_false_of_not_eq_true hb)
      let e : ℕ × ℕ × ℕ := (p + 1, member, t)
      have hcons : ∀ {c m}, valTraceHas trRest c m → valTraceHas (e :: trRest) c m :=
        fun h => valTraceHas_append_right (tr₁ := [e]) h
      refine ⟨e :: trRest,
        valTraceOk_cons hokRest ?_ (fun h0 => (Nat.succ_ne_zero p h0).elim),
        ⟨t, by simp [e]⟩⟩
      · refine Or.inr ⟨?_, ?_⟩
        · simpa [e, Nat.pred_succ, unpairComp_eq] using hcons hhasOp'
        · intro i hi
          simpa [e, Nat.pred_succ, unpairComp_eq] using
            (hhasBits' i hi).imp_right hcons

end DomainTheory.DataTypesAsLattices
