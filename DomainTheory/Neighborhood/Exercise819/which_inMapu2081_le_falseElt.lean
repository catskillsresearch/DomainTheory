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


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Exercise326

universe u




section SumHelpers

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-- `which(in₁ y) ≤ false`: a right-injected element's tag never reaches `true`. -/
theorem which_inMap₁_le_falseElt (y : V₁.Element) :
    (whichMap V₀ V₁ h₀ h₁).toElementMap ((inMap₁ (h₀ := h₀) (h₁ := h₁)).toElementMap y)
      ≤ Example23.falseElt := by
  intro Z hZ
  rcases (Example12.mem_iff Z).mp
      (((whichMap V₀ V₁ h₀ h₁).toElementMap
        ((inMap₁ (h₀ := h₀) (h₁ := h₁)).toElementMap y)).sub hZ) with rfl | rfl | rfl
  · exact Example23.falseElt.master_mem
  · exfalso
    obtain ⟨X, hX, hmem⟩ := which_mem_zero.mp hZ
    obtain ⟨Y, _, hY0, _, hsub⟩ := hmem
    exact not_inj₁_subset_inj₀ (h₁ Y hY0) hsub
  · show Example23.falseElt.mem Example12.one
    exact Or.inr rfl

end SumHelpers
end DomainTheory.Neighborhood
