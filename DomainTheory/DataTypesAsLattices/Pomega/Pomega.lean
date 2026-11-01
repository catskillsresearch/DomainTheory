module

public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

abbrev Pomega := Set ℕ

def botElem : Pomega := ∅

def topElem : Pomega := Set.univ

@[simp] theorem mem_botElem (n : ℕ) : n ∈ botElem ↔ False := by simp [botElem]

@[simp] theorem mem_topElem (n : ℕ) : n ∈ topElem := Set.mem_univ n

end DomainTheory.DataTypesAsLattices
