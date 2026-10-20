/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Example84
import DomainTheory.Neighborhood.Definition83
import DomainTheory.Neighborhood.Exercise510
import DomainTheory.Neighborhood.Example84b.Basic
import DomainTheory.Neighborhood.Example84b.smashFadeInner_mem
import DomainTheory.Neighborhood.Example84b.smashRetraction_mem


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}





section Smash






/-- **`smashRetraction`'s closed form.** `smash(z) = z` if neither coordinate is `⊥`; otherwise
`smash(z) = ⊥`. -/
theorem smashRetraction_mem_iff {z : (prod D E).Element} {Z : Set (α ⊕ β)} :
    (smashRetraction.toElementMap z).mem Z ↔
      (prod D E).mem Z ∧
        (Z = (prod D E).master ∨ (z.fst ≠ D.bot ∧ z.snd ≠ E.bot ∧ z.mem Z)) := by
  rw [smashRetraction_mem, smashFadeInner_mem]
  constructor
  · rintro ⟨hPZ, hZeq | ⟨hx, hPZ', hZeq' | ⟨hy, hzZ⟩⟩⟩
    · exact ⟨hPZ, Or.inl hZeq⟩
    · exact ⟨hPZ, Or.inl hZeq'⟩
    · exact ⟨hPZ, Or.inr ⟨hx, hy, hzZ⟩⟩
  · rintro ⟨hPZ, hZeq | ⟨hx, hy, hzZ⟩⟩
    · exact ⟨hPZ, Or.inl hZeq⟩
    · exact ⟨hPZ, Or.inr ⟨hx, hPZ, Or.inr ⟨hy, hzZ⟩⟩⟩

end Smash
end DomainTheory.Neighborhood
