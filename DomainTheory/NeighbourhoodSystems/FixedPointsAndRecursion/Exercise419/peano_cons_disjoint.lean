/-ai
The two successor operations on binary strings have disjoint ranges: a string headed by false differs from a string headed by true.

The list constructors separate the two forms.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise419

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44


/-- **Exercise 4.19 — Peano (ii′) for `{0,1}*`.** The two successor ranges are disjoint:
`0σ ≠ 1τ`. -/
theorem peano_cons_disjoint (σ τ : Str) : (false :: σ) ≠ (true :: τ) := by
  simp

end DomainTheory.NeighbourhoodSystems.Exercise419
