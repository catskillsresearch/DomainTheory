/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Congr.orderIsoOfMutualInverse
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Congr.funSpaceCongrOrderIso
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Congr.ofIso_symm_comp_ofIso
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Congr.ofIso_comp_ofIso_symm
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Congr.funSpaceCongr_hji
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Congr.funSpaceCongr_hij

@[expose] public section

/-!
# Exercise 8.25 (Scott 1981, PRG-19, §8), toolkit — function-space congruence and currying

Two small general-purpose isomorphism-manipulation tools, needed to assemble the final closing
argument of Exercise 8.25 (`D ≅ D → V`, `V × V ≅ V` `⟹` `D × D ≅ D`, `D ≅ D → D`):

* **`funSpace_congr`**: `𝒟₀ ≅ 𝒟₀'`, `𝒟₁ ≅ 𝒟₁'` `⟹` `(𝒟₀ → 𝒟₁) ≅ (𝒟₀' → 𝒟₁')`, built from
  `Proposition810b.lean`'s Hom-bifunctor `expMap` (`f ↦ k∘f∘h`) applied to the two `ApproximableMap`s
  `ofIso e₀.symm`/`ofIso e₁` coming from the given order-isomorphisms, using `expMap`'s functor laws
  (`expMap_comp`/`expMap_id`) to see that the two induced maps are *exact* mutual inverses
  (`orderIsoOfMutualInverse`, a small standalone gadget: two approximable maps composing to the
  identity *on the nose* in both directions give an order-isomorphism of element types — arguably
  missing general infrastructure, provided here).
* **`curry_isomorphic`**: `(𝒟₀ × 𝒟₁ → 𝒟₂) ≅ (𝒟₀ → (𝒟₁ → 𝒟₂))`, Theorem 3.12's `curryIso`
  (`Table55.lean`) restated as a domain isomorphism.

Everything is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

/-! ### A standalone gadget: exact mutual inverses give an order-isomorphism -/


/-! ### `ofIso e` and `ofIso e.symm` are exact mutual inverses -/



/-! ### `funSpace` congruence -/




/-! ### Currying, as a domain isomorphism -/
end DomainTheory.NeighbourhoodSystems
