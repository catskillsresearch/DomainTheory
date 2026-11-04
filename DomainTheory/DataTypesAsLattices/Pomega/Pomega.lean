module -- shake: keep-all

public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Insert

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

abbrev Pomega := Set ℕ

def botElem : Pomega := ∅

def topElem : Pomega := Set.univ

@[simp] theorem mem_botElem (n : ℕ) : n ∈ botElem ↔ False := by simp [botElem]

@[simp] theorem mem_topElem (n : ℕ) : n ∈ topElem := Set.mem_univ n

namespace topElem

theorem pos : ∃ n, n + 1 ∈ topElem :=
  ⟨0, Set.mem_univ 1⟩

end topElem

end DomainTheory.DataTypesAsLattices

