/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Example43
import DomainTheory.Neighborhood.Exercise326
import DomainTheory.Neighborhood.Exercise511
import DomainTheory.Neighborhood.Theorem41
import DomainTheory.Neighborhood.ApproximableExercises
import Mathlib.Computability.PartrecBasis
import DomainTheory.Neighborhood.Theorem56Full.Basic
import DomainTheory.Neighborhood.Theorem56Full.component_tupleMap
import DomainTheory.Neighborhood.Theorem56Full.realizer_value
import DomainTheory.Neighborhood.Theorem56Full.component_tupleMap_ge


namespace DomainTheory.Neighborhood.Theorem56Full

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap
open DomainTheory.Neighborhood.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.Neighborhood.Exercise326 (cond)
open DomainTheory.Neighborhood.Exercise511 (head tail push)



















/-- The tuple of realisers, applied to a total argument, is arg-like. -/
theorem tupleMap_argLike {m nn : ℕ} (φg : Fin nn → ApproximableMap 𝒩 N)
    (g : Fin nn → List.Vector ℕ m →. ℕ) (hg : ∀ i, LamDef (φg i) (g i)) (v : List.Vector ℕ m) :
    ArgLike ((tupleMap nn φg).toElementMap (vecElem v)) := by
  intro i
  by_cases hi : i < nn
  · rw [component_tupleMap nn φg (vecElem v) i hi]; exact realizer_value (hg ⟨i, hi⟩) v
  · rw [component_tupleMap_ge nn φg (vecElem v) i (Nat.le_of_not_lt hi)]; exact Or.inl rfl

end DomainTheory.Neighborhood.Theorem56Full
