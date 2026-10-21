/-ai
Given a master set and a finite list of input-output pairs, the intersection of the relevant outputs at a set X is computed inside that master. The empty list yields the master. A head pair contributes the set of points that lie in the head output whenever X is contained in the head input, and that set is met with the intersection for the tail.
ai-/
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

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- Scott's intersection `⋂ {Yᵢ ∣ X ⊆ Xᵢ}` of the outputs whose input is coarser than `X`, taken
inside the master neighbourhood `Δ₁` (so the empty intersection is `Δ₁`, per the convention 1.1a).
Indexed by the list `L` of `(Xᵢ, Yᵢ)` pairs. -/
def interYs (m : Set β) : List (Set α × Set β) → Set α → Set β
  | [], _ => m
  | p :: L, X => {z | X ⊆ p.1 → z ∈ p.2} ∩ interYs m L X

end DomainTheory.NeighbourhoodSystems
