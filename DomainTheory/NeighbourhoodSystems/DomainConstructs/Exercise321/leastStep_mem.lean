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


theorem leastStep_mem {Y : Set α} {Z : Set β} (hY : V₀.mem Y) (hZ : V₁.mem Z) :
    leastStep Y Z hY hZ ∈ step Y Z := by
  have := leastMap_mem_stepFun (V₀ := V₀) (V₁ := V₁)
    (L := [(Y, Z)]) (by rintro p hp; rw [List.mem_singleton] at hp; subst hp; exact ⟨hY, hZ⟩)
    (stepCons hZ)
  rw [stepFun_singleton] at this
  exact this

end DomainTheory.NeighbourhoodSystems
