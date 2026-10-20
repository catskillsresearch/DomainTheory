/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Definition711
import DomainTheory.Neighborhood.Definition72
import DomainTheory.Neighborhood.ApproximableExercises
import DomainTheory.Neighborhood.Product
import DomainTheory.Neighborhood.Proposition710
import DomainTheory.Neighborhood.Theorem74
import DomainTheory.Neighborhood.Lemma615
import Mathlib.Tactic
import DomainTheory.Neighborhood.Proposition712.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)













variable (P : ComputablePresentation V)

/-- **Proposition 7.12 — code form of singleton membership.** `{↑X_n}` relates to `Y_k` iff some
index in `dl k` lies above `X_n`. -/
theorem PDsingletonApproxMap_rel_Ypd_iff {n k : ℕ} :
    ((PDsingletonApproxMap (V := V))).rel (P.X n) (V.Ypd P k) ↔
      ∃ b ∈ decodeList k, P.X n ⊆ P.X b := by
  rw [PDsingletonApproxMap_rel (hX := P.mem_X n), PDmem_singleton, PowerDomain_mem]
  constructor
  · rintro ⟨Y, hYpr, _, hsub⟩
    have hn : P.X n ∈ V.upSet Y := ⟨P.mem_X n, hYpr.2⟩
    obtain ⟨b, hb, hPab⟩ := (V.mem_Ypd P).mp (hsub hn)
    exact ⟨b, hb, hPab.2⟩
  · intro ⟨b, hb, hnb⟩
    refine ⟨P.X b, ⟨P.mem_X b, hnb⟩, V.Ypd_isPDmem P k,
      (V.upSet_subset_Ypd_iff P).mpr ⟨b, hb, subset_rfl⟩⟩

end NeighborhoodSystem
end DomainTheory.Neighborhood
