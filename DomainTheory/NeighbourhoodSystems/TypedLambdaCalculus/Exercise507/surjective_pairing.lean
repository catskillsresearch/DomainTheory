/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.FunctionSpace
public import DomainTheory.Neighborhood.Exercise507.Basic

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise507

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap

variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- **Surjective pairing.** Every element `z : D₀ × D₁` is recovered from its projections:
`⟨p₀(z), p₁(z)⟩ = z`. This is what makes `p₀`, `p₁`, `pair` enough to encode the product. -/
theorem surjective_pairing (z : (prod V₀ V₁).Element) :
    pair ((proj₀ V₀ V₁).toElementMap z) ((proj₁ V₀ V₁).toElementMap z) = z := by
  rw [toElementMap_proj₀, toElementMap_proj₁, pair_fst_snd]

end DomainTheory.Neighborhood.Exercise507
