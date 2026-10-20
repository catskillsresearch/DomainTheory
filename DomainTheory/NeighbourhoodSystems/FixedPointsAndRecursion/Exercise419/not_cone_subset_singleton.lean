module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise419

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44

/-- A cone is never contained in a singleton (it has at least two elements). -/
theorem not_cone_subset_singleton (τ σ : Str) : ¬ cone τ ⊆ ({σ} : Set Str) := by
  intro h
  have h1 : τ ∈ ({σ} : Set Str) := h (by simp [mem_cone])
  have h2 : (τ ++ [true]) ∈ ({σ} : Set Str) := h (by simp [mem_cone])
  rw [Set.mem_singleton_iff] at h1 h2
  have : τ = τ ++ [true] := h1.trans h2.symm
  simp at this

end DomainTheory.NeighbourhoodSystems.Exercise419
