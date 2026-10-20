/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise326
public import DomainTheory.Neighborhood.Exercise319Sum
public import DomainTheory.Neighborhood.Exercise326Sum.Basic

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise326

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap

variable {α β : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}




theorem condSumEmb_toElementMap (t : TD.Element) (x : V₀.Element) (y : V₁.Element) :
    (condSumEmb V₀ V₁ h₀ h₁).toElementMap (pair t (pair x y))
      = pair t (pair ((inMap₀ (h₀ := h₀) (h₁ := h₁)).toElementMap x)
          ((inMap₁ (h₀ := h₀) (h₁ := h₁)).toElementMap y)) := by
  simp only [condSumEmb, toElementMap_paired, toElementMap_comp, toElementMap_proj₀,
    toElementMap_proj₁, fst_pair, snd_pair]

end DomainTheory.Neighborhood.Exercise326
