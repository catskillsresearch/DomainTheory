/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Distrib.copair
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Distrib.copairProj
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Distrib.distribMap
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Distrib.copair_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Distrib.prod_mem_nonempty

@[expose] public section

/-!
# Exercise 3.24(iii)(iv) (Scott 1981, PRG-19, §3) — sum/product "isomorphisms" that are only maps

Scott's list of isomorphisms ends with two entries and the caveat *"If some of the above are not
true, perhaps at least some mapping relationships can be established."* Parts (iii) and (iv) are
exactly those: with Scott's **separated** sum `𝒟₀ + 𝒟₁` (a fresh bottom `Λ` glued below two disjoint
copies), neither

* (iii) `𝒟₀ × (𝒟₁ + 𝒟₂) ≅ (𝒟₀ × 𝒟₁) + (𝒟₀ × 𝒟₂)`, nor
* (iv)  `(𝒟₀ + 𝒟₁) → 𝒟₂ ≅ (𝒟₀ → 𝒟₂) × (𝒟₁ → 𝒟₂)`

holds as a genuine isomorphism. (For (iv): `inᵢ(⊥)` lies strictly above the sum's bottom, so a map
`h` is *not* recoverable from `h ∘ in₀` and `h ∘ in₁` — the value `h(⊥)` is free. For (iii): the
left side has, for each `x ∈ |𝒟₀|`, an element `⟨x, ⊥⟩` incomparable to both cones, which the right
side lacks.)

What *is* true are the canonical **mapping relationships**:

* **(iv)** the *copairing* `[a, b] : 𝒟₀ + 𝒟₁ → 𝒟₂` with `[a,b] ∘ inᵢ = a, b` (`copair`,
  `copair_comp_inMap₀/₁`), exhibiting `(𝒟₀→𝒟₂) × (𝒟₁→𝒟₂)` as a **retract** of `(𝒟₀+𝒟₁) → 𝒟₂`
  (`copairProj_copair`); and
* **(iii)** the canonical *distribution* map
  `(𝒟₀ × 𝒟₁) + (𝒟₀ × 𝒟₂) → 𝒟₀ × (𝒟₁ + 𝒟₂)` (`distribMap`), `inᵢ⟨x, u⟩ ↦ ⟨x, inᵢ u⟩`.

The development re-uses Exercise 3.18's injections/projections and the structural extraction lemmas of
Exercise 3.19.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-! ### (iv) — the copairing `[a, b] : 𝒟₀ + 𝒟₁ → 𝒟₂`. -/




/-! ### (iii) — the canonical distribution map. -/


end DomainTheory.NeighbourhoodSystems
