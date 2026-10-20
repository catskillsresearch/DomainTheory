/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Example43
public import DomainTheory.Neighborhood.Exercise326
public import DomainTheory.Neighborhood.Exercise511
public import DomainTheory.Neighborhood.Theorem41
public import DomainTheory.Neighborhood.ApproximableExercises
public import Mathlib.Computability.PartrecBasis
import all Mathlib.Computability.PartrecBasis
public import DomainTheory.Neighborhood.Theorem56Full.Basic
public import DomainTheory.Neighborhood.Theorem56Full.lamDef_coe_val
public import DomainTheory.Neighborhood.Theorem56Full.push_natElem_vecElem
public import DomainTheory.Neighborhood.Theorem56Full.searchMap_rec

@[expose] public section


namespace DomainTheory.Neighborhood.Theorem56Full

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap
open DomainTheory.Neighborhood.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.Neighborhood.Exercise326 (cond)
open DomainTheory.Neighborhood.Exercise511 (head tail push)
























section Rfind

variable (φf : ApproximableMap 𝒩 N)





/-- **Search step (found).** If `f(k ::ᵥ v) = 0`, the search returns the counter `k`. -/
theorem searchMap_step_found {n : ℕ} {f : List.Vector ℕ (n + 1) → ℕ}
    (hf : LamDef φf (f : List.Vector ℕ (n + 1) →. ℕ)) (v : List.Vector ℕ n) (k : ℕ)
    (h0 : f (k ::ᵥ v) = 0) :
    (searchMap φf).toElementMap (vecElem (k ::ᵥ v)) = natElem k := by
  rw [← push_natElem_vecElem, searchMap_rec, Exercise511.head_push, Exercise511.tail_push,
    push_natElem_vecElem, lamDef_coe_val hf (k ::ᵥ v), h0, zeroMap_natElem_zero,
    Exercise326.cond_true]

end Rfind
end DomainTheory.Neighborhood.Theorem56Full
