module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.boxShift_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem boxShift_expansive {a : Pomega} (ha : Closure a) (x : Pomega) :
    x ⊆ funOf (boxShift a) x := by
  rw [boxShift_app]
  intro k hk
  cases k with
  | zero => exact Or.inl rfl
  | succ k =>
    refine Or.inr ⟨k, ?_, rfl⟩
    have hx : predSet x ⊆ funOf a (predSet x) := by
      have := funOf_monotone_left ha.out.1 (predSet x)
      rwa [Icomb_app] at this
    exact hx hk

end DomainTheory.DataTypesAsLattices
