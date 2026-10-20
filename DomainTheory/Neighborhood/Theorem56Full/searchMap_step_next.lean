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
import DomainTheory.Neighborhood.Theorem56Full.lamDef_coe_val
import DomainTheory.Neighborhood.Theorem56Full.push_natElem_vecElem
import DomainTheory.Neighborhood.Theorem56Full.searchMap_rec


namespace DomainTheory.Neighborhood.Theorem56Full

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap
open DomainTheory.Neighborhood.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.Neighborhood.Exercise326 (cond)
open DomainTheory.Neighborhood.Exercise511 (head tail push)
























section Rfind

variable (φf : ApproximableMap 𝒩 N)





/-- **Search step (continue).** If `f(k ::ᵥ v) ≠ 0`, the search advances to counter `k + 1`. -/
theorem searchMap_step_next {n : ℕ} {f : List.Vector ℕ (n + 1) → ℕ}
    (hf : LamDef φf (f : List.Vector ℕ (n + 1) →. ℕ)) (v : List.Vector ℕ n) (k : ℕ)
    (hne : f (k ::ᵥ v) ≠ 0) :
    (searchMap φf).toElementMap (vecElem (k ::ᵥ v)) =
      (searchMap φf).toElementMap (vecElem ((k + 1) ::ᵥ v)) := by
  obtain ⟨m, hm⟩ : ∃ m, f (k ::ᵥ v) = m + 1 := ⟨f (k ::ᵥ v) - 1, by omega⟩
  rw [← push_natElem_vecElem, searchMap_rec, Exercise511.head_push, Exercise511.tail_push,
    push_natElem_vecElem, lamDef_coe_val hf (k ::ᵥ v), hm, zeroMap_natElem_succ,
    Exercise326.cond_false, succMap_natElem, push_natElem_vecElem]

end Rfind
end DomainTheory.Neighborhood.Theorem56Full
