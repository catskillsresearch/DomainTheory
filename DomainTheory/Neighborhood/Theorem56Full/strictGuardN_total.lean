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
import DomainTheory.Neighborhood.Theorem56Full.guard1_total


namespace DomainTheory.Neighborhood.Theorem56Full

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap
open DomainTheory.Neighborhood.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.Neighborhood.Exercise326 (cond)
open DomainTheory.Neighborhood.Exercise511 (head tail push)













/-- On arguments whose first `n` coordinates are all total, the guard is transparent. -/
theorem strictGuardN_total (n : ℕ) (φ : ApproximableMap 𝒩 N) (z : 𝒩.Element)
    (h : ∀ j, j < n → ∃ k, component z j = natElem k) :
    (strictGuardN n φ).toElementMap z = φ.toElementMap z := by
  induction n with
  | zero => rfl
  | succ m ih =>
    obtain ⟨k, hk⟩ := h m (Nat.lt_succ_self m)
    rw [strictGuardN, guard1_total m _ z hk]
    exact ih (fun j hj => h j (Nat.lt_succ_of_lt hj))

end DomainTheory.Neighborhood.Theorem56Full
