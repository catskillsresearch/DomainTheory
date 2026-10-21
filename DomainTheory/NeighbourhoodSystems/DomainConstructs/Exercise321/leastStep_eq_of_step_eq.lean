/-ai
Equal step neighbourhoods have the same least single-step map.

Each least map lies in its own step and hence, by the equality of the steps, in the other step, and each least map lies below every member of its step, so the two least maps lie below one another.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise321.Basic
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
