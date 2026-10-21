/-ai
Strict currying is the order isomorphism from strict maps out of the smash product to strict maps into the strict function space, with forward map the curry combinator, inverse the uncurry combinator, and the two round trips the corresponding identities. If the curry of the first map lies below the curry of the second, a relation of the first map becomes, through the uncurry-curry identity, a curried relation on the left preimage and the step of the right preimage; the inequality moves that relation to the second curry, and reassembling it with the original domain returns a relation of the second map by the same identity. If the first map lies below the second, a curried relation unpacks its strict-function neighbourhood as a list of steps, and each witnessing relation of the first map is sent to the second map.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_master
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_mem_bot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_smashPair
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.StrictMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstep
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_sstep
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_sstepFun
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstepFun_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstep_master_eq
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.strictFun
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.strictFun_master
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.toStrictMap_rel
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_toStrictFilter
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashCurryMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashUncurryMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashUncurry_curry
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashCurry_uncurry

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise510

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

/-- **Exercise 5.10 (Scott 1981, PRG-19) — the adjunction.** The strict currying combinator is an
order isomorphism `((𝒟₀ ⊗ 𝒟₁) →⊥ 𝒟₂) ≃ (𝒟₀ →⊥ (𝒟₁ →⊥ 𝒟₂))`: the smash product is left adjoint to
the strict function space. -/
def smashCurryEquiv (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (V₂ : NeighborhoodSystem γ) :
    StrictMap (smash V₀ V₁) V₂ ≃o StrictMap V₀ (strictFun V₁ V₂) where
  toFun := smashCurryMap
  invFun := smashUncurryMap
  left_inv := smashUncurry_curry
  right_inv := smashCurry_uncurry
  map_rel_iff' := by
    intro g g'
    constructor
    · intro hcurry W Z hrel
      have h1 : (smashCurryMap g).1.rel (Sum.inl ⁻¹' W) (sstep (Sum.inr ⁻¹' W) Z) := by
        have hu : (smashUncurryMap (smashCurryMap g)).1.rel W Z := by
          rw [smashUncurry_curry]; exact hrel
        exact hu.2
      have h2 := hcurry _ _ h1
      have hu' : (smashUncurryMap (smashCurryMap g')).1.rel W Z := ⟨g.1.rel_dom hrel, h2⟩
      rw [smashUncurry_curry] at hu'
      exact hu'
    · intro hg X N hrel
      obtain ⟨hX, hN, hmem⟩ := hrel
      refine ⟨hX, hN, ?_⟩
      obtain ⟨⟨L, hL, rfl⟩, _⟩ := hN
      intro p hp
      obtain ⟨hY, hmm⟩ := hmem p hp
      obtain ⟨W, hWmem, hWrel⟩ := hmm
      exact ⟨hY, W, hWmem, hg W p.2 hWrel⟩

end DomainTheory.NeighbourhoodSystems.Exercise510
