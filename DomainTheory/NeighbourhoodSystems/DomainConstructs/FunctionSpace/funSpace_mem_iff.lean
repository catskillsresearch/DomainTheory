/-ai
A set of approximable maps is a function-space neighborhood if and only if it is nonempty and equals the step neighborhood of a finite list of neighborhood pairs.

This is the defining clause of the function space.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.BasicInst3
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_step
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.stepFun
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_stepFun
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.stepFun_nil
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.step_master_eq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpace_master

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem funSpace_mem_iff {W : Set (ApproximableMap V₀ V₁)} :
    (funSpace V₀ V₁).mem W ↔
      (∃ L : List (Set α × Set β), (∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2) ∧ W = stepFun L)
        ∧ W.Nonempty := Iff.rfl

end DomainTheory.NeighbourhoodSystems
