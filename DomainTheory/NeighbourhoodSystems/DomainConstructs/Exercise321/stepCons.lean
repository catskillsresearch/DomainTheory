module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise321.interYs_single_subset_eq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise321.interYs_single_not_subset_eq

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- Consistency (`hcons`) for a single step `[Y, Z]`: the intersection over the relevant outputs is
either `Z` (sharp input) or `Δ₂` (blunt input), both neighbourhoods. -/
theorem stepCons {Y : Set α} {Z : Set β} (hZ : V₁.mem Z) :
    ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master [(Y, Z)] X) := by
  intro X _
  by_cases hXY : X ⊆ Y
  · rw [interYs_single_subset_eq hZ hXY]; exact hZ
  · rw [interYs_single_not_subset_eq hXY]; exact V₁.master_mem

end DomainTheory.NeighbourhoodSystems
