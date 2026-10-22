module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.boxShift_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem zero_mem_boxShift_app (a x : Pomega) : (0 : ℕ) ∈ funOf (boxShift a) x := by
  rw [boxShift_app]
  exact Or.inl (by simp [ofNat])

end DomainTheory.DataTypesAsLattices
