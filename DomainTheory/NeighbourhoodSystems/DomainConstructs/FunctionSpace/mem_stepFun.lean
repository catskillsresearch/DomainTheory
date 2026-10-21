/-ai
An approximable map lies in the step neighborhood of a list exactly when it relates every pair in the list.

This is the defining clause of a step neighborhood.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.BasicInst3
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_step
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.stepFun

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

@[simp] theorem mem_stepFun {L : List (Set α × Set β)} {f : ApproximableMap V₀ V₁} :
    f ∈ stepFun L ↔ ∀ p ∈ L, f.rel p.1 p.2 := Iff.rfl

end DomainTheory.NeighbourhoodSystems
