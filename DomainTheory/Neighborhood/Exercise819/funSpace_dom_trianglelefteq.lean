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
import DomainTheory.Neighborhood.Exercise819.expMap_mono_left


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Exercise326

universe u


section General

variable {α β γ δ : Type*}

/-- **Contravariant functoriality of `⊴` in the function-space's domain argument.** `A ⊴ B ⟹
(A → C) ⊴ (B → C)` for any `C`: precompose/postcompose with the given projection pair via
`expMap`. -/
theorem funSpace_dom_trianglelefteq {A : NeighborhoodSystem α} {B : NeighborhoodSystem β}
    (C : NeighborhoodSystem γ) (h : A ⊴ B) : funSpace A C ⊴ funSpace B C := by
  obtain ⟨D', hD'B, ⟨eAD'⟩⟩ := h
  set p : ProjPair A B := (ProjPair.ofIso eAD').comp (ProjPair.ofSubsystem hD'B) with hp
  refine trianglelefteq_of_projectionPair (expMap p.proj (idMap C)) (expMap p.inj (idMap C))
    ?_ ?_
  · have hcomp := (expMap_comp p.proj (idMap C) p.inj (idMap C)).symm
    rw [hcomp, p.proj_comp_inj, idMap_comp]
    exact expMap_id
  · calc (expMap p.proj (idMap C)).comp (expMap p.inj (idMap C))
        = expMap (p.inj.comp p.proj) ((idMap C).comp (idMap C)) :=
          (expMap_comp p.inj (idMap C) p.proj (idMap C)).symm
      _ ≤ expMap (idMap B) ((idMap C).comp (idMap C)) :=
          expMap_mono_left p.inj_comp_proj_le _
      _ = expMap (idMap B) (idMap C) := by rw [idMap_comp]
      _ = idMap (funSpace B C) := expMap_id

end General
end DomainTheory.Neighborhood
