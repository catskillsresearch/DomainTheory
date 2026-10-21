/-ai
Any neighbourhood system A is a retract of the product of A with B, by the embedding that pairs an element with bottom and the first projection.

Those two maps form a projection pair.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise820.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise820.proju2080_comp_embedFst
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise820.embedFst_comp_proju2080_le

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u v


section Prod

variable {α : Type u} {β : Type v} (A : NeighborhoodSystem α) (B : NeighborhoodSystem β)


/-- **`A ⊴ prod A B`**, via `a ↦ ⟨a, ⊥⟩` / `proj₀`. -/
theorem trianglelefteq_prod_fst : A ⊴ prod A B :=
  trianglelefteq_of_projectionPair (embedFst A B) (proj₀ A B) (proj₀_comp_embedFst A B)
    (embedFst_comp_proj₀_le A B)

end Prod
end DomainTheory.NeighbourhoodSystems
