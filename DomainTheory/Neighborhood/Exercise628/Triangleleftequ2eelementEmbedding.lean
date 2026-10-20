/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Lemma615
import DomainTheory.Neighborhood.Proposition612
import DomainTheory.Neighborhood.Exercise628.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}



/-- **`D ⊴ E` yields an order embedding `|D| ↪o |E|`.** Unfold `⊴` to an iso `|D| ≅o |D'|` onto a
subdomain `D' ◁ E`, turn `D' ◁ E` into Proposition 6.12's projection pair, and compose its
injection embedding with the iso. Choice-free. -/
theorem Trianglelefteq.elementEmbedding (h : D ⊴ E) :
    Nonempty (D.Element ↪o E.Element) := by
  obtain ⟨D', hsub, ⟨e⟩⟩ := h
  exact ⟨e.toOrderEmbedding.trans
    (projElementEmbedding hsub.inj hsub.proj hsub.proj_comp_inj)⟩

end DomainTheory.Neighborhood
