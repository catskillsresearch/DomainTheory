module

public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import DomainTheory.DataTypesAsLattices.Pomega.mem_botElem
public import DomainTheory.DataTypesAsLattices.Pomega.mem_topElem
public import DomainTheory.DataTypesAsLattices.Pomega.e

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

@[simp] theorem mem_e {n k : ℕ} : k ∈ e n ↔ n.testBit k := Iff.rfl

end DomainTheory.DataTypesAsLattices
