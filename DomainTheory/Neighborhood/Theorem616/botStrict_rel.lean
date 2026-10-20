/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem69
import DomainTheory.Neighborhood.Proposition67
import DomainTheory.Neighborhood.Lemma615
import DomainTheory.Neighborhood.Exercise408
import DomainTheory.Neighborhood.Theorem616.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap DomainTheory.Neighborhood.Exercise510

universe w


/-- The strict map represented by `⊥` of the strict function space relates `X` to `Y` exactly when
`X` is a neighbourhood and `Y` is the master output: it is the constant-`⊥` (least) strict map. -/
theorem botStrict_rel {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    {X : Set α} {Y : Set β} :
    (toStrictMap (strictFun V₀ V₁).bot).1.rel X Y ↔ V₀.mem X ∧ Y = V₁.master := by
  rw [toStrictMap_rel, NeighborhoodSystem.mem_bot, strictFun_master]
  constructor
  · intro h
    have hcb : (⟨constMap V₀ V₁.bot, isStrict_constBot⟩ : StrictMap V₀ V₁) ∈ sstep X Y := by
      rw [h]; exact Set.mem_univ _
    rw [mem_sstep, constMap_rel, NeighborhoodSystem.mem_bot] at hcb
    exact hcb
  · rintro ⟨hX, rfl⟩
    exact sstep_cod_master hX

end DomainTheory.Neighborhood
