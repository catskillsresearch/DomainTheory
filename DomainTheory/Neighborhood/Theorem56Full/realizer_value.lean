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


namespace DomainTheory.Neighborhood.Theorem56Full

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap
open DomainTheory.Neighborhood.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.Neighborhood.Exercise326 (cond)
open DomainTheory.Neighborhood.Exercise511 (head tail push)


















/-- The value a realiser takes on a total argument is total-or-`⊥` (arg-like). -/
theorem realizer_value {n : ℕ} {φ : ApproximableMap 𝒩 N} {f : List.Vector ℕ n →. ℕ}
    (h : LamDef φ f) (v : List.Vector ℕ n) :
    φ.toElementMap (vecElem v) = N.bot ∨ ∃ k, φ.toElementMap (vecElem v) = natElem k := by
  by_cases hd : (f v).Dom
  · exact Or.inr ⟨(f v).get hd, h.defined v _ (Part.get_mem hd)⟩
  · exact Or.inl (h.undef v hd)

end DomainTheory.Neighborhood.Theorem56Full
