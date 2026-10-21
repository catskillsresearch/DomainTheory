/-ai
A cone of binary strings is never equal to a singleton.

Equality would make the cone a subset of the singleton, and no cone is contained in a singleton.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.not_cone_subset_singleton

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise419

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44

/-- A cone is never equal to a singleton. -/
theorem cone_ne_singleton (τ σ : Str) : cone τ ≠ ({σ} : Set Str) := by
  intro h
  exact not_cone_subset_singleton τ σ (h ▸ subset_rfl)

end DomainTheory.NeighbourhoodSystems.Exercise419
