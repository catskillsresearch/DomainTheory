module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise321.leastStep
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise321.interYs_single_subset_eq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise321.interYs_single_not_subset_eq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise321.stepCons
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise321.leastStep_mem
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise321.leastStep_le

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- The least elements of equal step neighbourhoods coincide. -/
theorem leastStep_eq_of_step_eq {Y : Set α} {Z : Set β} (hY : V₀.mem Y) (hZ : V₁.mem Z)
    {Y' : Set α} {Z' : Set β} (hY' : V₀.mem Y') (hZ' : V₁.mem Z')
    (h : (step Y Z : Set (ApproximableMap V₀ V₁)) = step Y' Z') :
    leastStep Y Z hY hZ = leastStep Y' Z' hY' hZ' := by
  apply le_antisymm
  · exact leastStep_le hY hZ (h ▸ leastStep_mem hY' hZ')
  · exact leastStep_le hY' hZ' (h.symm ▸ leastStep_mem hY hZ)

end DomainTheory.NeighbourhoodSystems
