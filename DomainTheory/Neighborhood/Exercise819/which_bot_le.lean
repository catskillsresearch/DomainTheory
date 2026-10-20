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
import DomainTheory.Neighborhood.Exercise819.TD_bot_eq_botElt


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Exercise326

universe u




section SumHelpers

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-- `which(⊥) ≤ ⊥`: the basepoint carries no tag information. Only the third `whichGuard` disjunct
applies at `W = (sum V₀ V₁ h₀ h₁).master`, forcing the output to `master`. -/
theorem which_bot_le :
    (whichMap V₀ V₁ h₀ h₁).toElementMap (sum V₀ V₁ h₀ h₁).bot ≤ Example23.botElt := by
  rw [← TD_bot_eq_botElt]
  refine toElementMap_bot_le _ ?_
  intro Y hg
  exact whichGuard_masterC hg.2.2 rfl

end SumHelpers
end DomainTheory.Neighborhood
