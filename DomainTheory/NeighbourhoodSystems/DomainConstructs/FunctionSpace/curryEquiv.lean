/-ai
Currying is an order isomorphism from maps out of a product to maps into the function space, with inverse uncurrying, by the two round-trip identities. If the curry of one map lies below the curry of another, a related pair of the first becomes, after uncurrying the curried relation on the left preimage and the step of the right preimage, a related pair of the second. In the other direction, the inequality of the original maps sends each section membership that expresses the curried relation to the corresponding membership for the larger map.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.BasicInst3
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.step
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_step
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_stepFun
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.stepFun_nil
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.step_master_eq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpace_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.toApproxMap_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_toFilter
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpaceEquiv_apply
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpaceEquiv_symm_apply
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.interYs_nil
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.leastMap_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.gSection_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.curry
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.curry_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.uncurry
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.uncurry_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.uncurry_curry
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.curry_uncurry

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

/-- **Theorem 3.12 (Scott 1981, PRG-19).** `curry` is an order-isomorphism between
`|𝒟₀ × 𝒟₁ → 𝒟₂|` and `|𝒟₀ → (𝒟₁ → 𝒟₂)|`. -/
def curryEquiv (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (prod V₀ V₁) V₂ ≃o ApproximableMap V₀ (funSpace V₁ V₂) where
  toFun := curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry
  map_rel_iff' := by
    intro g g'
    constructor
    · intro hcurry W Z hrel
      have h1 : (curry g).rel (Sum.inl ⁻¹' W) (step (Sum.inr ⁻¹' W) Z) := by
        have hu : (uncurry (curry g)).rel W Z := by rw [uncurry_curry]; exact hrel
        exact hu.2
      have h2 := hcurry _ _ h1
      have hu' : (uncurry (curry g')).rel W Z := ⟨g.rel_dom hrel, h2⟩
      rw [uncurry_curry] at hu'
      exact hu'
    · intro hg X W hrel
      obtain ⟨hX, hW, hmem⟩ := hrel
      refine ⟨hX, hW, ?_⟩
      obtain ⟨⟨L, hL, rfl⟩, _⟩ := hW
      intro p hp
      have hgrel : g.rel (prodNbhd X p.1) p.2 := hmem p hp
      exact hg _ _ hgrel

end DomainTheory.NeighbourhoodSystems
