module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Enumeration.ValTrace
public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Enumeration.Gcomb
public import DomainTheory.DataTypesAsLattices.Enumeration.REPredu2eexists_param
public import DomainTheory.DataTypesAsLattices.Computability.primrecPred_bool
public import DomainTheory.DataTypesAsLattices.Enumeration.Gcomb_more

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def valTraceG (tr : ValTrace) : Prop :=
  ∀ e ∈ tr, e.1 = 0 → e.2.1 ∈ Gcomb

namespace valTraceG

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

/-- Membership in `G` along a finite trace is r.e. via one `evaln` stage. -/
theorem re : REPred valTraceG := by
  have hf : Partrec fun k : ℕ =>
      (Part.assert (k ∈ Gcomb) fun _ => Part.some (0 : ℕ)) :=
    Gcomb.isRE.out.map (Computable.const (0 : ℕ)).to₂
  obtain ⟨c, hc⟩ := Code.exists_code.1 (Partrec.nat_iff.1 hf)
  have hbitP : PrimrecPred fun q : (ℕ × ℕ × ℕ) × ℕ =>
      q.1.1 ≠ 0 ∨ (evaln q.2 c q.1.2.1).isSome = true :=
    (Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 0)).not.or
      (primrecPred_bool (Primrec.option_isSome.comp
        (primrec_evaln.comp
          (Primrec.pair
            (Primrec.pair Primrec.snd (Primrec.const c))
            (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))))))
  have hbit : PrimrecRel fun (e : ℕ × ℕ × ℕ) (s : ℕ) =>
      e.1 ≠ 0 ∨ (evaln s c e.2.1).isSome = true :=
    hbitP.of_eq fun _ => Iff.rfl
  have hall : PrimrecRel fun (tr : ValTrace) (s : ℕ) =>
      ∀ e ∈ tr, e.1 ≠ 0 ∨ (evaln s c e.2.1).isSome = true :=
    PrimrecRel.forall_mem_list hbit
  have hex : REPred fun tr : ValTrace =>
      ∃ s, ∀ e ∈ tr, e.1 ≠ 0 ∨ (evaln s c e.2.1).isSome = true :=
    REPred.exists_param (α := ValTrace)
      (hall.comp Primrec.fst Primrec.snd).computablePred.to_re
  refine _root_.REPred.of_eq hex fun tr => ⟨fun ⟨s, hs⟩ e he he0 => ?_, fun hG => ?_⟩
  · have hsome : (evaln s c e.2.1).isSome = true :=
      (hs e he).resolve_left fun hne => hne he0
    obtain ⟨val, hval⟩ := Option.isSome_iff_exists.mp hsome
    have : val ∈ Code.eval c e.2.1 :=
      evaln_sound (by simpa [Option.mem_def] using hval)
    have : val ∈ (Part.assert (e.2.1 ∈ Gcomb) fun _ => Part.some (0 : ℕ)) := by
      simpa [hc] using this
    exact (Part.mem_assert_iff.mp this).1
  · induction tr with
    | nil => exact ⟨0, fun _ he => by cases he⟩
    | cons e tr ih =>
      obtain ⟨s2, hs2⟩ := ih fun e' he' h0 => hG e' (List.mem_cons_of_mem _ he') h0
      by_cases h0 : e.1 = 0
      · have hmem : 0 ∈ Code.eval c e.2.1 := by
          rw [hc]
          exact Part.mem_assert_iff.mpr ⟨hG e (List.mem_cons_self) h0,
            Part.mem_some_iff.mpr rfl⟩
        obtain ⟨s1, hs1⟩ := evaln_complete.mp hmem
        refine ⟨max s1 s2, fun e' he' => ?_⟩
        rcases List.mem_cons.mp he' with rfl | he'
        · exact Or.inr (Option.isSome_of_mem (evaln_mono (Nat.le_max_left s1 s2) hs1))
        · rcases hs2 e' he' with hne | hsome
          · exact Or.inl hne
          · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
            exact Or.inr (Option.isSome_of_mem (evaln_mono (Nat.le_max_right s1 s2) hv))
      · refine ⟨s2, fun e' he' => ?_⟩
        rcases List.mem_cons.mp he' with rfl | he'
        · exact Or.inl h0
        · exact hs2 e' he'

end valTraceG

end DomainTheory.DataTypesAsLattices
