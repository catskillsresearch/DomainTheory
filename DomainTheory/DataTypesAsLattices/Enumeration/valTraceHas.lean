module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Enumeration.ValTrace
public import DomainTheory.DataTypesAsLattices.Pomega.e

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def valTraceHas (tr : ValTrace) (code member : ℕ) : Prop :=
  ∃ t, (code, member, t) ∈ tr

namespace valTraceHas

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem append_left {tr₁ tr₂ : ValTrace} {c m : ℕ}
    (h : valTraceHas tr₁ c m) : valTraceHas (tr₁ ++ tr₂) c m := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t, List.mem_append.mpr (Or.inl ht)⟩

theorem append_right {tr₁ tr₂ : ValTrace} {c m : ℕ}
    (h : valTraceHas tr₂ c m) : valTraceHas (tr₁ ++ tr₂) c m := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t, List.mem_append.mpr (Or.inr ht)⟩

theorem iff (tr : ValTrace) (c m : ℕ) :
    valTraceHas tr c m ↔ ∃ e ∈ tr, e.1 = c ∧ e.2.1 = m := by
  constructor
  · intro ⟨t, ht⟩
    exact ⟨(c, m, t), ht, rfl, rfl⟩
  · intro ⟨e, he, hc, hm⟩
    exact ⟨e.2.2, by cases e; cases hc; cases hm; exact he⟩

end valTraceHas

end DomainTheory.DataTypesAsLattices
