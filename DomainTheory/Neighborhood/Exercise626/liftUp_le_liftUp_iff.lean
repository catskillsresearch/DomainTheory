/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise621
import DomainTheory.Neighborhood.Exercise626.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap DomainTheory.Neighborhood.Exercise619
open DomainTheory.Neighborhood.Example62 DomainTheory.Neighborhood.ExampleB
open DomainTheory.Neighborhood.Exercise510

namespace Exercise619

variable {D : NeighborhoodSystem Str}










variable {hD : ∀ X, D.mem X → X.Nonempty}








/-- `liftUp` is an order embedding: `liftUp x ⊑ liftUp y ↔ x ⊑ y`. -/
theorem liftUp_le_liftUp_iff {x y : D.Element} :
    liftUp (hD := hD) x ≤ liftUp (hD := hD) y ↔ x ≤ y := by
  constructor
  · intro h X hX
    have hmem := h (embBit false X) (Or.inr ⟨X, hX, rfl⟩)
    rcases hmem with h0 | ⟨X', hX', heq⟩
    · exact absurd (h0.symm ▸ nil_mem_liftTokMaster) nil_not_mem_embBit
    · rw [embBit_injective heq]; exact hX'
  · rintro h W (rfl | ⟨X, hX, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨X, h X hX, rfl⟩

end Exercise619
end DomainTheory.Neighborhood
