/-ai
The empty binary string is not a successor.

The list constructors separate the empty string from a cons cell.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise419

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44


/-- **Exercise 4.19 — Peano (i) for `{0,1}*`.** `Λ` is not a successor: `[] ≠ b :: σ`. -/
theorem peano_nil_ne_cons (b : Bool) (σ : Str) : ([] : Str) ≠ b :: σ := by
  simp

end DomainTheory.NeighbourhoodSystems.Exercise419
