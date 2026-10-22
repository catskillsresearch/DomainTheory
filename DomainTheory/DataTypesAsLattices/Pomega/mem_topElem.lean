/-ai
Every natural number belongs to the top element.

This is membership in the universal set.
ai-/
module

public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import DomainTheory.DataTypesAsLattices.Pomega.topElem
public import DomainTheory.DataTypesAsLattices.Pomega.mem_botElem

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

@[simp] theorem mem_topElem (n : ℕ) : n ∈ topElem := Set.mem_univ n

end DomainTheory.DataTypesAsLattices
