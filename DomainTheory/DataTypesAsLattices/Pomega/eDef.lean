module

public import Mathlib.Data.Nat.Bitwise
public import DomainTheory.DataTypesAsLattices.Pomega.Pomega

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def e (n : ℕ) : Pomega := {k | n.testBit k}

@[simp] theorem mem_e {n k : ℕ} : k ∈ e n ↔ n.testBit k := Iff.rfl

end DomainTheory.DataTypesAsLattices
