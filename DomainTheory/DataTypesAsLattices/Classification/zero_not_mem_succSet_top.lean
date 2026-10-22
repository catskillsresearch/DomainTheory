/-ai
Zero does not belong to ⊤ + 1.

A member of ⊤ + 1 is some successor n + 1, and a successor is never zero.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace


theorem zero_not_mem_succSet_top : 0 ∉ succSet topElem := by
  intro h
  obtain ⟨n, _, hn⟩ := h
  exact Nat.succ_ne_zero n hn.symm

end DomainTheory.DataTypesAsLattices
