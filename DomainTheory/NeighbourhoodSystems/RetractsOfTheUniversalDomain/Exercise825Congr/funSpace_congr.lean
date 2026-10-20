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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Congr.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}










/-- **`funSpace` is a congruence for `≅ᴰ`.** `𝒟₀ ≅ᴰ 𝒟₀'`, `𝒟₁ ≅ᴰ 𝒟₁'` `⟹`
`(𝒟₀ → 𝒟₁) ≅ᴰ (𝒟₀' → 𝒟₁')`. -/
theorem funSpace_congr (h0 : V₀ ≅ᴰ V₀') (h1 : V₁ ≅ᴰ V₁') :
    funSpace V₀ V₁ ≅ᴰ funSpace V₀' V₁' :=
  h0.elim fun e0 => h1.elim fun e1 => ⟨funSpaceCongrOrderIso e0 e1⟩

end DomainTheory.NeighbourhoodSystems
