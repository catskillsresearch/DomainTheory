/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise213
import DomainTheory.Neighborhood.Exercise215.Basic
import DomainTheory.Neighborhood.Exercise215.botElt_ne_topElt


namespace DomainTheory.Neighborhood.Exercise215

open DomainTheory.Neighborhood NeighborhoodSystem
















/-- **The opens of `|𝒪|`.** `{⊥}` is not open: `⊥` is the generic point. (The basic neighbourhood of
`⊥` is `[Δ] = |𝒪|`, which is not contained in `{⊥}` because it also contains `⊤`.) -/
theorem not_isOpen_singleton_botElt : ¬ IsOpen ({botElt} : Set O.Element) := by
  intro h
  obtain ⟨X, hX, hsub⟩ := h botElt rfl
  rw [mem_botElt] at hX
  subst hX
  have htop : topElt ∈ ({botElt} : Set O.Element) :=
    hsub (show topElt ∈ O.basicOpen Set.univ from (O_master ▸ topElt.master_mem))
  exact botElt_ne_topElt (Set.mem_singleton_iff.mp htop).symm

end DomainTheory.Neighborhood.Exercise215
