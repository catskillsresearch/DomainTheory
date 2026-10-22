/-ai
If a is a closure, every set x is contained in the application of the shift of a to x.

The application unfolds as the union of the singleton zero with a successor set. Zero lies in the left summand. A successor lies in the right summand once its predecessor lies in a applied to the predecessor set, and that inclusion is the expansiveness of a coming from left monotonicity of application and the identity action of the identity combinator.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.boxShift_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem boxShift_expansive {a : Pomega} (ha : IsClosure a) (x : Pomega) :
    x ⊆ funOf (boxShift a) x := by
  rw [boxShift_app]
  intro k hk
  cases k with
  | zero => exact Or.inl rfl
  | succ k =>
    refine Or.inr ⟨k, ?_, rfl⟩
    have hx : predSet x ⊆ funOf a (predSet x) := by
      have := funOf_monotone_left ha.1 (predSet x)
      rwa [Icomb_app] at this
    exact hx hk

end DomainTheory.DataTypesAsLattices
