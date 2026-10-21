/-ai
An approximable map relates every input neighbourhood to the master neighbourhood of the codomain.

Monotonicity applied to the master relation enlarges the master input to the given neighbourhood and keeps the master output.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}










variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}





















variable {V₂ : NeighborhoodSystem γ}

open ApproximableMap


/-- An approximable map relates any input neighbourhood to the master output `Δ₁`. -/
theorem ApproximableMap.rel_master (f : ApproximableMap V₀ V₁) {X : Set α} (hX : V₀.mem X) :
    f.rel X V₁.master :=
  f.mono f.master_rel (V₀.sub_master hX) subset_rfl hX V₁.master_mem

end DomainTheory.NeighbourhoodSystems
