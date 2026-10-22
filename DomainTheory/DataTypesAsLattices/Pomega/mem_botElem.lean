module

public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import DomainTheory.DataTypesAsLattices.Pomega.botElem

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

@[simp] theorem mem_botElem (n : ℕ) : n ∈ botElem ↔ False := by simp [botElem]

end DomainTheory.DataTypesAsLattices
