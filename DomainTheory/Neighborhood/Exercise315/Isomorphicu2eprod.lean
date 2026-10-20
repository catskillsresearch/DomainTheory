/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Product
import DomainTheory.Neighborhood.Exercise315.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem

variable {α β γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

















/-- **Exercise 3.15(iii).** `𝒟₀ ≅ 𝒟₀'` and `𝒟₁ ≅ 𝒟₁'` imply `𝒟₀ × 𝒟₁ ≅ 𝒟₀' × 𝒟₁'`. -/
theorem Isomorphic.prod (h₀ : V₀ ≅ᴰ V₀') (h₁ : V₁ ≅ᴰ V₁') : prod V₀ V₁ ≅ᴰ prod V₀' V₁' :=
  h₀.elim fun e₀ => h₁.elim fun e₁ => ⟨prodCongrD e₀ e₁⟩

end DomainTheory.Neighborhood
