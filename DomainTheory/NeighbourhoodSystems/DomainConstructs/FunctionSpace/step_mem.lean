module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.BasicInst3
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.step
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_step
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_stepFun
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.stepFun_nil
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.stepFun_singleton
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.step_master_eq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpace_master

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- A step neighbourhood `[X, Y]` is a neighbourhood of the function space (non-empty: it contains
the constant map `constMap V₀ (↑Y)`). -/
theorem step_mem {X : Set α} {Y : Set β} (hX : V₀.mem X) (hY : V₁.mem Y) :
    (funSpace V₀ V₁).mem (step X Y) := by
  refine ⟨⟨[(X, Y)], ?_, (stepFun_singleton X Y).symm⟩,
    ⟨constMap V₀ (V₁.principal hY), ?_⟩⟩
  · intro p hp; rw [List.mem_singleton] at hp; subst hp; exact ⟨hX, hY⟩
  · show (constMap V₀ (V₁.principal hY)).rel X Y
    exact ⟨hX, hY, subset_rfl⟩

end DomainTheory.NeighbourhoodSystems
