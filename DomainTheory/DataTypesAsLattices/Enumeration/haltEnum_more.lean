module

public import DomainTheory.DataTypesAsLattices.Enumeration.haltEnum
public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2eexists
public import DomainTheory.DataTypesAsLattices.Enumeration.primrec_haltEnum

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

namespace haltEnum

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem succ_iff (m : ℕ) :
    (∃ t, haltEnum t = m + 1) ↔ (eval (Denumerable.ofNat Code m) 0).Dom := by
  constructor
  · intro ⟨t, ht⟩
    have hs : (evaln t.unpair.2 (Denumerable.ofNat Code t.unpair.1) 0).isSome = true := by
      by_contra h
      have : haltEnum t = 0 := by
        simp [haltEnum, Bool.eq_false_of_not_eq_true h]
      omega
    have : haltEnum t = t.unpair.1 + 1 := by simp [haltEnum, hs]
    have hm : t.unpair.1 = m := by omega
    obtain ⟨val, hval⟩ := Option.isSome_iff_exists.mp hs
    exact Part.dom_iff_mem.mpr ⟨val, evaln_sound (by simpa [hm] using hval)⟩
  · intro hdom
    obtain ⟨val, hval⟩ := Part.dom_iff_mem.mp hdom
    obtain ⟨s, hs⟩ := evaln_complete.mp hval
    refine ⟨Nat.pair m s, ?_⟩
    simp [haltEnum, Nat.unpair_pair, Option.isSome_of_mem hs]

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem range_not_computable :
    ¬ComputablePred fun m => ∃ t, haltEnum t = m := by
  intro hc
  have := hc.choose
  have hsucc : ComputablePred fun n : ℕ => ∃ t, haltEnum t = n + 1 :=
    Computable.computablePred
      ((ComputablePred.decide hc).comp Primrec.succ.to_comp)
  have hn : ComputablePred fun n : ℕ =>
      (eval (Denumerable.ofNat Code n) 0).Dom :=
    hsucc.of_eq fun n => haltEnum.succ_iff n
  have := hn.choose
  have : DecidablePred fun c : Code => (eval c 0).Dom :=
    fun c => decidable_of_iff
      (eval (Denumerable.ofNat Code (encode c)) 0).Dom
      (by simp [Denumerable.ofNat_encode])
  exact ComputablePred.halting_problem (n := 0)
    (Computable.computablePred
      ((ComputablePred.decide hn).comp Computable.encode |>.of_eq fun c => by
        simp [Denumerable.ofNat_encode]))

theorem range_re : REPred fun m => ∃ t, haltEnum t = m :=
  REPred.exists (p := fun m t => haltEnum t = m)
    ((Primrec.eq.comp (primrec_haltEnum.comp Primrec.snd) Primrec.fst).computablePred.to_re)

end haltEnum

end DomainTheory.DataTypesAsLattices
