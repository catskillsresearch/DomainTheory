/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Table55
import DomainTheory.Neighborhood.Theorem51.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

namespace Theorem51


theorem var_snd (x : V₀.Element) (y : V₁.Element) :
    (proj₁ V₀ V₁).toElementMap (pair x y) = y := by rw [toElementMap_proj₁, snd_pair]

end Theorem51
end DomainTheory.Neighborhood
