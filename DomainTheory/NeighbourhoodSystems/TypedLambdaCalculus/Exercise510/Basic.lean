/-ai
This file gathers and re-exports the smash product, the strict pairing and the collapse of bottom elements, the strict function space, and the strict curry and uncurry of Exercise 5.10. It records Scott's request to show that the smash product is a neighbourhood system, that the elements of the strict function space are exactly the strict maps, and that strict maps into a strict function space correspond to strict maps out of the smash product.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.SmashProper
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashPair
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.IsStrict
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstep
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstepFun
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.strictFun
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.toStrictMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.toStrictFilter
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.strictFunEquiv
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashSection
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashCurryMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashUncurryMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashCurryEquiv
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.inter_ne_master_left
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.inter_ne_master_right
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_master
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_mem_proper
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_mem_bot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_smashPair
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.exists_proper_of_ne_bot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.eq_bot_of_no_proper
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashPair_eq_bot_iff
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashPair_mono
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.principal_master_eq_bot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashPair_bot_left
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashPair_bot_right
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.isStrict_iff_apply_bot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mono
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.isStrict_constBot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.StrictMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_sstep
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_sstepFun
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstepFun_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstepFun_cons
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstepFun_append
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstepFun_singleton
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstep_master_eq
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstep_inter_right
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstep_subset
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.strictFun_master
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.strictFun_mem_iff
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstep_mem_of_mem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.strictFun_mem_inter
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstepFun_up_closed
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.strictFun_mem_up_closed
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_sstepFun_iff
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.toStrictMap_rel
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_toStrictFilter
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_mem_prodNbhd_form
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashPair_principal_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashSection_rel
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashSection_mono
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.isStrict_smashSection
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.rel_sstepFun_iff
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstep_cod_master
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.section_uncurry_rel
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashUncurry_curry
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smashCurry_uncurry

@[expose] public section

/-!
# Exercise 5.10 (Scott 1981, PRG-19, §5) — the smash product and the strict function space

> Suppose `𝒟₀` and `𝒟₁` are neighbourhood systems over disjoint sets `Δ₀` and `Δ₁`. Define the
> *smash product* `𝒟₀ ⊗ 𝒟₁` with neighbourhoods
> `{Δ₀ ∪ Δ₁} ∪ {X ∪ Y ∣ X ∈ 𝒟₀ ∖ {Δ₀} and Y ∈ 𝒟₁ ∖ {Δ₁}}`.
> Show that this *is* a neighbourhood system. Define `(𝒟₀ →⊥ 𝒟₁)` so that `|𝒟₀ →⊥ 𝒟₁|` consists
> exactly of the *strict functions*. By introducing appropriate combinators, show that
> `(𝒟₀ →⊥ (𝒟₁ →⊥ 𝒟₂))` and `((𝒟₀ ⊗ 𝒟₁) →⊥ 𝒟₂)` are isomorphic.

We model the disjoint union of token sets by the **sum type** `α ⊕ β`, exactly as for the ordinary
product (`Domain/Neighborhood/Product.lean`), reusing `prodNbhd X Y = Sum.inl '' X ∪ Sum.inr '' Y`
and its algebra (`prodNbhd_inter`, `prodNbhd_subset_iff`, `prodNbhd_injective`).

This file is organised as follows.

* **The smash product** `smash V₀ V₁` (`§ smash`): a genuine neighbourhood system. The neighbourhoods
  are the master `Δ₀ ∪ Δ₁` together with the *proper* product neighbourhoods `X ∪ Y` whose factors are
  both *proper* (`X ≠ Δ₀`, `Y ≠ Δ₁`). Closure under consistent intersection is the new content: the
  consistency witness rules out the degenerate cases, and a proper factor stays proper under
  intersection.
* **The smash collapses bottoms** (`§ elements`): the element `smashPair x y` (the strict pairing) and
  the order-isomorphism showing `|𝒟₀ ⊗ 𝒟₁|` is the *smash* of the pointed domains — every element is
  either `⊥` or a pair `⟨x, y⟩` of *non-`⊥`* elements.
* **The strict function space** `strictFun V₀ V₁` (`§ strict`): a neighbourhood system whose elements
  are exactly the *strict* approximable maps (`IsStrict f`, i.e. `f(⊥) = ⊥`). We realise it as the
  function space generated only by step neighbourhoods `[X, Y]` with *proper* input `X`, and prove the
  representation `strictFunEquiv : |𝒟₀ →⊥ 𝒟₁| ≃o {f ∣ IsStrict f}`.
* **The adjunction** (`§ iso`): the "appropriate combinators" Scott asks for — a strict curry
  `smashCurryMap` and strict uncurry `smashUncurryMap` — assembled into the order-isomorphism
  `smashCurryEquiv : ((𝒟₀ ⊗ 𝒟₁) →⊥ 𝒟₂) ≃o (𝒟₀ →⊥ (𝒟₁ →⊥ 𝒟₂))`. The decisive computation is
  `section_uncurry_rel`: `g(⟨x, y⟩⊗) = curry⊥(g)(x)(y)`, with the boundary (a master factor) handled
  by strictness — exactly the bottom-gluing the smash performs.

The *data* (`smash`, `strictFun`, `smashCurryMap`, `smashUncurryMap`) and the representation
`strictFunEquiv` are **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`); `Classical.choice`
enters only the `smashCurryEquiv` *proof*, through the genuinely-classical `X = Δ₀?` / `Y = Δ₁?`
boundary case analysis.
-/

namespace DomainTheory.NeighbourhoodSystems.Exercise510

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

/-! ### The smash product `𝒟₀ ⊗ 𝒟₁`. -/


variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}







/-! ### The smash collapses bottoms: the strict pairing `⟨x, y⟩⊗`.

The smash identifies all elements that have a `⊥` in either coordinate. We realise this by the *strict
pairing* `smashPair x y`: when both `x, y` are non-`⊥` it is the genuine pair `⟨x, y⟩`, and when either
is `⊥` it collapses to `⊥` (`smashPair_eq_bot_iff`). Every element of `|𝒟₀ ⊗ 𝒟₁|` arises this way. -/










/-! ### The strict function space `(𝒟₀ →⊥ 𝒟₁)`.

A map `f : 𝒟₀ → 𝒟₁` is **strict** when `f(⊥) = ⊥`. In relational terms (since `f(⊥)` is the filter
`{Y ∣ Δ₀ f Y}`), this says `f` relates the master input `Δ₀` only to the master output `Δ₁`:
`Δ₀ f Y ⟹ Y = Δ₁`.

We realise `(𝒟₀ →⊥ 𝒟₁)` as the function space whose *tokens* are the **strict** approximable maps and
whose neighbourhoods are the non-empty finite intersections of step sets `[X, Y] = {f ∣ X f Y}`. The
crucial point — making `|𝒟₀ →⊥ 𝒟₁|` consist *exactly* of the strict functions — is automatic: a step
`[Δ₀, Y]` with `Y ≠ Δ₁` contains *no* strict map, so it is empty, hence never a neighbourhood; thus no
filter can force a non-strict value at `⊥`. The representation `strictFunEquiv` then mirrors
Theorem 3.10. -/






























/-! ### The adjunction `(𝒟₀ →⊥ (𝒟₁ →⊥ 𝒟₂)) ≅ ((𝒟₀ ⊗ 𝒟₁) →⊥ 𝒟₂)`.

The smash product is *left adjoint* to the strict function space: strict maps out of a smash product
are the same as strict maps into a strict function space. We realise the iso with the "appropriate
combinators" Scott asks for — a *strict curry* and *strict uncurry* — connected by the computation
`g(⟨x, y⟩⊗) = (curry g)(x)(y)`.

The decisive computation is `smashPair_principal_apply`: for *proper* `X, Y`, applying `g` to the
strict pairing of the principal elements is the same as `g` relating the proper neighbourhood
`X ∪ Y`. At the bottom (a master factor) the strict pairing collapses to `⊥`, where strictness forces
the master output — exactly the gluing the smash performs. -/

variable {V₂ : NeighborhoodSystem γ}










/-! ### The roundtrip identities and the adjunction isomorphism. -/





end DomainTheory.NeighbourhoodSystems.Exercise510
