/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Basic
import DomainTheory.Neighborhood.Theorem41
import Mathlib.Data.Set.Insert
import DomainTheory.Neighborhood.Exercise722.Basic


namespace DomainTheory.Neighborhood

namespace Exercise722

open NeighborhoodSystem ApproximableMap

























/-- The embedding is **injective**: distinct words give distinct elements of `|S|`. (If
`emb σ = emb τ` then `emb τ` contains `{σ}`, forcing `τ = σ`.) So `Σ` genuinely *embeds* into `|S|`. -/
theorem emb_injective : Function.Injective emb := by
  intro σ τ h
  have hmem : (emb τ).mem {σ} := h ▸ (⟨InS.singleton σ, rfl⟩ : (emb σ).mem {σ})
  exact (Set.mem_singleton_iff.mp hmem.2).symm

end Exercise722
end DomainTheory.Neighborhood
