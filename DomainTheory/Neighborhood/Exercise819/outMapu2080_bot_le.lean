/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise817
import DomainTheory.Neighborhood.Proposition810b
import DomainTheory.Neighborhood.Exercise326Sum
import DomainTheory.Neighborhood.Exercise315
import DomainTheory.Neighborhood.Exercise819.Basic
import DomainTheory.Neighborhood.Exercise819.toElementMap_bot_le


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Exercise326

universe u




section SumHelpers

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-- `out₀(⊥) ≤ ⊥`: the basepoint carries no left-hand information. -/
theorem outMap₀_bot_le :
    (outMap₀ (h₀ := h₀) (h₁ := h₁)).toElementMap (sum V₀ V₁ h₀ h₁).bot ≤ V₀.bot := by
  refine toElementMap_bot_le _ ?_
  intro Y hg
  refine Set.Subset.antisymm (V₀.sub_master hg.2.1) ?_
  have h2 : leftPart V₀ (sumMaster V₀ V₁) ⊆ Y := hg.2.2
  rwa [leftPart_sumMaster] at h2

end SumHelpers
end DomainTheory.Neighborhood
