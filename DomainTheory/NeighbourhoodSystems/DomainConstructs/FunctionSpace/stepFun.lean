module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.BasicInst3
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_step

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- A finite intersection of step sets, indexed by a list of `(X, Y)` pairs. -/
def stepFun (L : List (Set α × Set β)) : Set (ApproximableMap V₀ V₁) :=
  {f | ∀ p ∈ L, f.rel p.1 p.2}

end DomainTheory.NeighbourhoodSystems
