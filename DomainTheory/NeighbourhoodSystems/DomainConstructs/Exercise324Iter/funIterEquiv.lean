module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Iter.mapOfSeq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Iter.toElementMap_mapOfSeq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Iter.projComp_mono
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Iter.le_of_projComp_le

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **Exercise 3.24(ii) (Scott 1981, PRG-19).** The order-isomorphism on approximable maps
`Hom(𝒟₀, 𝒟₁^∞) ≃o (ℕ → Hom(𝒟₀, 𝒟₁))`, `f ↦ (n ↦ projₙ ∘ f)`. -/
def funIterEquiv (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    ApproximableMap V₀ (iterSys V₁) ≃o (∀ _ : ℕ, ApproximableMap V₀ V₁) where
  toFun f := fun n => (projN V₁ n).comp f
  invFun g := mapOfSeq g
  left_inv f := by
    apply ext_of_toElementMap
    intro x
    rw [toElementMap_mapOfSeq]
    have hfun : (fun i => ((projN V₁ i).comp f).toElementMap x)
        = (fun i => component (f.toElementMap x) i) := by
      funext i; rw [toElementMap_comp, toElementMap_projN]
    rw [hfun, ofSeq_component]
  right_inv g := by
    funext n
    apply ext_of_toElementMap
    intro x
    rw [toElementMap_comp, toElementMap_mapOfSeq, toElementMap_projN, component_ofSeq]
  map_rel_iff' := by
    intro f f'
    constructor
    · intro h; exact le_of_projComp_le (fun n => h n)
    · intro h n; exact projComp_mono h n

end DomainTheory.NeighbourhoodSystems
