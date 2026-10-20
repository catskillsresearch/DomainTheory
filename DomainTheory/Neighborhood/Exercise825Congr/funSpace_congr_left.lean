/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Proposition810b
public import DomainTheory.Neighborhood.Exercise324
public import DomainTheory.Neighborhood.Table55
public import DomainTheory.Neighborhood.Exercise825Congr.Basic
public import DomainTheory.Neighborhood.Exercise825Congr.funSpace_congr

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}










/-- **`funSpace` congruence, domain slot.** `𝒟₀ ≅ᴰ 𝒟₀'` `⟹` `(𝒟₀ → 𝒟₁) ≅ᴰ (𝒟₀' → 𝒟₁)`. -/
theorem funSpace_congr_left (h0 : V₀ ≅ᴰ V₀') : funSpace V₀ V₁ ≅ᴰ funSpace V₀' V₁ :=
  funSpace_congr h0 (Isomorphic.refl V₁)

end DomainTheory.Neighborhood
