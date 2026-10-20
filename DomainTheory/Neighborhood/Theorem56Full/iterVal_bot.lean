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
import DomainTheory.Neighborhood.Theorem56Full.iterVal_zero
import DomainTheory.Neighborhood.Theorem56Full.iterVal_succ


namespace DomainTheory.Neighborhood.Theorem56Full

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap
open DomainTheory.Neighborhood.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.Neighborhood.Exercise326 (cond)
open DomainTheory.Neighborhood.Exercise511 (head tail push)
























section Rfind

variable (φf : ApproximableMap 𝒩 N)







/-- Along a *no-zero* trace, every finite approximant returns `⊥` (induction on the approximant
index, with the counter universally quantified since the search advances it). -/
theorem iterVal_bot {n : ℕ} {f : List.Vector ℕ (n + 1) → ℕ}
    (hf : LamDef φf (f : List.Vector ℕ (n + 1) →. ℕ)) (v : List.Vector ℕ n)
    (hdiv : ∀ k, f (k ::ᵥ v) ≠ 0) :
    ∀ m k, (toApproxMap ((findOp φf).iterElem m)).toElementMap (vecElem (k ::ᵥ v)) = N.bot := by
  intro m
  induction m with
  | zero => intro k; exact iterVal_zero φf (vecElem (k ::ᵥ v))
  | succ m ih =>
    intro k
    have hne := hdiv k
    obtain ⟨j, hj⟩ : ∃ j, f (k ::ᵥ v) = j + 1 := ⟨f (k ::ᵥ v) - 1, by omega⟩
    rw [← push_natElem_vecElem, iterVal_succ, Exercise511.head_push, Exercise511.tail_push,
      push_natElem_vecElem, lamDef_coe_val hf (k ::ᵥ v), hj, zeroMap_natElem_succ,
      Exercise326.cond_false, succMap_natElem, push_natElem_vecElem]
    exact ih (k + 1)

end Rfind
end DomainTheory.Neighborhood.Theorem56Full
