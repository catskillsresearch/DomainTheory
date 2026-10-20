/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise316
public import DomainTheory.Neighborhood.FunctionSpace
public import DomainTheory.Neighborhood.Exercise324Iter.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}









/-- **Exercise 3.24(ii).** `(𝒟₀ → 𝒟₁^∞) ≅ (𝒟₀ → 𝒟₁)^∞`. -/
theorem funIter_isomorphic : funSpace V₀ (iterSys V₁) ≅ᴰ iterSys (funSpace V₀ V₁) :=
  ⟨funIterIso V₀ V₁⟩

end DomainTheory.Neighborhood
