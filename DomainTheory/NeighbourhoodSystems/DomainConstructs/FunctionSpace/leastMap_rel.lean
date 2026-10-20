module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.BasicInst3
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_step
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_stepFun
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.stepFun_nil
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.step_master_eq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpace_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.toApproxMap_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_toFilter
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpaceEquiv_apply
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpaceEquiv_symm_apply
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.interYs
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.interYs_nil
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.leastMap

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

@[simp] theorem leastMap_rel {L : List (Set α × Set β)}
    {hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2}
    {hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)} {X : Set α} {Y : Set β} :
    (leastMap L hL hcons).rel X Y ↔ V₀.mem X ∧ V₁.mem Y ∧ interYs V₁.master L X ⊆ Y := Iff.rfl

end DomainTheory.NeighbourhoodSystems
