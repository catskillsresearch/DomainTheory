/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise621
import DomainTheory.Neighborhood.Lemma615
import DomainTheory.Neighborhood.Exercise627.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap DomainTheory.Neighborhood.Exercise619
open DomainTheory.Neighborhood.Example62 DomainTheory.Neighborhood.ExampleB
open DomainTheory.Neighborhood.Exercise510

namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}






variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem oplusTok_subsystem_sumTok (h₀ : ∀ X, D₀.mem X → X.Nonempty)
    (h₁ : ∀ Y, D₁.mem Y → Y.Nonempty) :
    oplusTok D₀ D₁ h₀ h₁ ◁ sumTok D₀ D₁ h₀ h₁ where
  master_eq := rfl
  sub := by
    rintro W (rfl | ⟨X, hX, -, rfl⟩ | ⟨Y, hY, -, rfl⟩)
    · exact Or.inl rfl
    · exact sumTok_mem_embF hX
    · exact sumTok_mem_embT hY
  inter_closed := by
    rintro W W' (rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩)
      (rfl | ⟨X', hX', hX'ne, rfl⟩ | ⟨Y', hY', hY'ne, rfl⟩) hInt
    · rw [Set.inter_self]; exact Or.inl rfl
    · rw [sumTokMaster_inter_embF hX']; exact oplusTok_mem_embF hX' hX'ne
    · rw [sumTokMaster_inter_embT hY']; exact oplusTok_mem_embT hY' hY'ne
    · rw [Set.inter_comm, sumTokMaster_inter_embF hX]; exact oplusTok_mem_embF hX hXne
    · rw [embBit_inter] at hInt ⊢
      exact oplusTok_mem_embF (sumTok_mem_embF_inv hInt)
        (inter_ne_of_ne_left (D₀.sub_master hX) hXne)
    · rw [embBit_inter_ne (show (false : Bool) ≠ true by decide)] at hInt
      exact absurd (sumTok_mem_nonempty hInt) Set.not_nonempty_empty
    · rw [Set.inter_comm, sumTokMaster_inter_embT hY]; exact oplusTok_mem_embT hY hYne
    · rw [embBit_inter_ne (show (true : Bool) ≠ false by decide)] at hInt
      exact absurd (sumTok_mem_nonempty hInt) Set.not_nonempty_empty
    · rw [embBit_inter] at hInt ⊢
      exact oplusTok_mem_embT (sumTok_mem_embT_inv hInt)
        (inter_ne_of_ne_left (D₁.sub_master hY) hYne)

end Exercise627
end DomainTheory.Neighborhood
