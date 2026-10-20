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
import DomainTheory.Neighborhood.Theorem56Full.eq_of_component_eq
import DomainTheory.Neighborhood.Theorem56Full.component_tupleMap
import DomainTheory.Neighborhood.Theorem56Full.component_vecElem_lt
import DomainTheory.Neighborhood.Theorem56Full.component_tupleMap_ge


namespace DomainTheory.Neighborhood.Theorem56Full

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap
open DomainTheory.Neighborhood.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.Neighborhood.Exercise326 (cond)
open DomainTheory.Neighborhood.Exercise511 (head tail push)



















/-- The tuple of realisers, applied to a total argument, equals `vecElem w` where `wᵢ = gᵢ(v)`. -/
theorem tupleMap_vecElem_eq {m nn : ℕ} (φg : Fin nn → ApproximableMap 𝒩 N)
    (g : Fin nn → List.Vector ℕ m →. ℕ) (hg : ∀ i, LamDef (φg i) (g i))
    (v : List.Vector ℕ m) (w : List.Vector ℕ nn) (hw : ∀ i, w.get i ∈ g i v) :
    (tupleMap nn φg).toElementMap (vecElem v) = vecElem w := by
  apply eq_of_component_eq
  intro i
  by_cases hi : i < nn
  · rw [component_tupleMap nn φg (vecElem v) i hi, component_vecElem_lt w hi]
    exact (hg ⟨i, hi⟩).defined v (w.get ⟨i, hi⟩) (hw ⟨i, hi⟩)
  · rw [component_tupleMap_ge nn φg (vecElem v) i (Nat.le_of_not_lt hi), component_vecElem,
      dite_eq_right hi]

end DomainTheory.Neighborhood.Theorem56Full
