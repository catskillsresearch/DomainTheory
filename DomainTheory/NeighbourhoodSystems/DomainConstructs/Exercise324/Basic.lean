/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324.funProdEquiv
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324.funProdIso

@[expose] public section

/-!
# Exercise 3.24 (Scott 1981, PRG-19, §3) — function-space isomorphisms

Scott asks to establish further isomorphisms. We formalize **(i)**:

`(𝒟₀ → (𝒟₁ × 𝒟₂)) ≅ (𝒟₀ → 𝒟₁) × (𝒟₀ → 𝒟₂)`.

The crux is the order-isomorphism on the *approximable maps* themselves,
`funProdEquiv : Hom(𝒟₀, 𝒟₁ × 𝒟₂) ≃o Hom(𝒟₀, 𝒟₁) × Hom(𝒟₀, 𝒟₂)`, given by
`h ↦ (p₀ ∘ h, p₁ ∘ h)` with inverse `⟨a, b⟩ ↦ ⟨a, b⟩` (Definition 3.3's `paired`/`proj`, and the
round-trips `paired_proj` / `proj_comp_paired`). Transporting through Theorem 3.10's `funSpaceEquiv`
and Proposition 3.2's `prodEquiv` gives the domain isomorphism `funProdIso`.

Everything is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


end DomainTheory.NeighbourhoodSystems
