/-ai
Any neighbourhood system B is a retract of the product of A with B, by the embedding that pairs bottom with an element and the second projection.

Those two maps form a projection pair.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise820.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise820.proju2081_comp_embedSnd
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise820.embedSnd_comp_proju2081_le

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u v


section Prod

variable {α : Type u} {β : Type v} (A : NeighborhoodSystem α) (B : NeighborhoodSystem β)


/-- **`B ⊴ prod A B`**, via `b ↦ ⟨⊥, b⟩` / `proj₁`. -/
theorem trianglelefteq_prod_snd : B ⊴ prod A B :=
  trianglelefteq_of_projectionPair (embedSnd A B) (proj₁ A B) (proj₁_comp_embedSnd A B)
    (embedSnd_comp_proj₁_le A B)

end Prod
end DomainTheory.NeighbourhoodSystems
