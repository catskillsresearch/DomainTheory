module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise321.leastStep
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise321.interYs_single_subset_eq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise321.interYs_single_not_subset_eq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise321.stepCons

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


theorem leastStep_le {Y : Set α} {Z : Set β} (hY : V₀.mem Y) (hZ : V₁.mem Z)
    {f : ApproximableMap V₀ V₁} (hf : f ∈ step Y Z) : leastStep Y Z hY hZ ≤ f := by
  apply leastMap_le
  rw [stepFun_singleton]; exact hf

end DomainTheory.NeighbourhoodSystems
