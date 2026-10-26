module

public import Mathlib.Computability.Halting
public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2eempty
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2etrue
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2ecomp
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2eand
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2eor
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2eexists
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.ValTrace
public import DomainTheory.DataTypesAsLattices.Enumeration.valTraceStruct
public import DomainTheory.DataTypesAsLattices.Enumeration.valTraceG
public import DomainTheory.DataTypesAsLattices.Enumeration.Gcomb
public import DomainTheory.DataTypesAsLattices.Enumeration.valTraceHas
public import DomainTheory.DataTypesAsLattices.Enumeration.valEntryJustified
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat
public import DomainTheory.DataTypesAsLattices.Enumeration.primrecPred_valTraceStruct
public import DomainTheory.DataTypesAsLattices.Enumeration.valTraceG_re

public import DomainTheory.DataTypesAsLattices.Enumeration.valEntryJustified_mono

public import DomainTheory.DataTypesAsLattices.Enumeration.unpairComp_eq

public import DomainTheory.DataTypesAsLattices.Enumeration.unpairComp

public import DomainTheory.DataTypesAsLattices.Enumeration.valTraceHas_append_left

public import DomainTheory.DataTypesAsLattices.Enumeration.valTraceHas_append_right

public import DomainTheory.DataTypesAsLattices.Graph.Basic.notation3
@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def valTraceOk (tr : ValTrace) : Prop :=
  valTraceStruct tr ∧ valTraceG tr

namespace valTraceOk

theorem empty : valTraceOk [] := by
  constructor
  · intro e he
    simp at he
  · intro e he _
    simp at he

theorem append {tr₁ tr₂ : ValTrace}
    (h₁ : valTraceOk tr₁) (h₂ : valTraceOk tr₂) :
    valTraceOk (tr₁ ++ tr₂) := by
  constructor
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact valEntryJustified_mono (fun _ _ => valTraceHas_append_left) (h₁.1 e he)
    · exact valEntryJustified_mono (fun _ _ => valTraceHas_append_right) (h₂.1 e he)
  · intro e he he0
    rcases List.mem_append.mp he with he | he
    · exact h₁.2 e he he0
    · exact h₂.2 e he he0

theorem cons {tr : ValTrace} {e : ℕ × ℕ × ℕ}
    (htr : valTraceOk tr) (hjust : valEntryJustified (e :: tr) e)
    (hg : e.1 = 0 → e.2.1 ∈ Gcomb) :
    valTraceOk (e :: tr) := by
  constructor
  · intro e' he'
    rcases List.mem_cons.mp he' with rfl | he'
    · exact hjust
    · exact valEntryJustified_mono
        (fun c m ⟨t, ht⟩ => ⟨t, List.mem_cons.mpr (Or.inr ht)⟩) (htr.1 e' he')
  · intro e' he' he0
    rcases List.mem_cons.mp he' with rfl | he'
    · exact hg he0
    · exact htr.2 e' he' he0

theorem zero (m : ℕ) (hm : m ∈ Gcomb) :
    valTraceOk [(0, m, 0)] ∧ valTraceHas [(0, m, 0)] 0 m := by
  refine ⟨⟨?_, ?_⟩, ⟨0, by simp⟩⟩
  · intro e he
    simp at he
    subst e
    exact Or.inl rfl
  · intro e he he0
    simp at he
    subst e
    exact hm

theorem sound {tr : ValTrace} (hok : valTraceOk tr) :
    ∀ {code member t}, (code, member, t) ∈ tr → member ∈ valNat code := by
  intro code member t hmem
  induction code using Nat.strongRecOn generalizing member t with
  | ind code ih =>
    have hjust := hok.1 (code, member, t) hmem
    cases code with
    | zero =>
      exact valNat.zero.symm ▸ hok.2 (0, member, t) hmem rfl
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
        exact valNat.succ p ▸ this

theorem re : REPred valTraceOk :=
  _root_.REPred.of_eq
    (REPred.and primrecPred_valTraceStruct.computablePred.to_re valTraceG_re)
    fun _ => Iff.rfl

end valTraceOk

end DomainTheory.DataTypesAsLattices
