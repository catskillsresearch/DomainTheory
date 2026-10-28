module

public import DomainTheory.DataTypesAsLattices.Enumeration.valTraceOk
public import DomainTheory.DataTypesAsLattices.Enumeration.exists_concat_traces
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat
public import DomainTheory.DataTypesAsLattices.Enumeration.valTraceHas
public import DomainTheory.DataTypesAsLattices.Enumeration.Gcomb
public import DomainTheory.DataTypesAsLattices.Enumeration.unpairComp
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Graph.Basic.notation3

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

namespace valTraceOk

theorem complete :
    ∀ code member, member ∈ valNat code →
      ∃ tr, valTraceOk tr ∧ valTraceHas tr code member := by
  intro code
  induction code using Nat.strongRecOn with
  | ind code ih =>
    intro member hm
    cases code with
    | zero =>
      obtain ⟨hok0, hhas0⟩ := valTraceOk.zero member (valNat.zero ▸ hm)
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
        valNat.succ p ▸ hm
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
      have hokRest : valTraceOk trRest := valTraceOk.append hokOp hokBits
      have hhasOp' : valTraceHas trRest (unpair p).1 (pair t member) :=
        valTraceHas.append_left hhasOp
      have hhasBits' : ∀ i < t + 1,
          t.testBit i = false ∨ valTraceHas trRest (unpair p).2 i := by
        intro i hi
        by_cases hb : t.testBit i = true
        · refine Or.inr (valTraceHas.append_right (hhasBits i ?_))
          simp [bits, List.mem_filter, List.mem_range, hi, hb]
        · exact Or.inl (Bool.eq_false_of_not_eq_true hb)
      let e : ℕ × ℕ × ℕ := (p + 1, member, t)
      have hcons : ∀ {c m}, valTraceHas trRest c m → valTraceHas (e :: trRest) c m :=
        fun h => valTraceHas.append_right (tr₁ := [e]) h
      refine ⟨e :: trRest,
        valTraceOk.cons hokRest ?_ (fun h0 => (Nat.succ_ne_zero p h0).elim),
        ⟨t, by simp [e]⟩⟩
      · refine Or.inr ⟨?_, ?_⟩
        · simpa [e, Nat.pred_succ, unpairComp.eq] using hcons hhasOp'
        · intro i hi
          simpa [e, Nat.pred_succ, unpairComp.eq] using
            (hhasBits' i hi).imp_right hcons

end valTraceOk

end DomainTheory.DataTypesAsLattices
