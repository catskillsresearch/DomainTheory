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
import DomainTheory.Neighborhood.Theorem56Full.component_push_zero
import DomainTheory.Neighborhood.Theorem56Full.component_push_succ


namespace DomainTheory.Neighborhood.Theorem56Full

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap
open DomainTheory.Neighborhood.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.Neighborhood.Exercise326 (cond)
open DomainTheory.Neighborhood.Exercise511 (head tail push)




















theorem push_natElem_vecElem {n : ℕ} (a : ℕ) (u : List.Vector ℕ n) :
    (push N).toElementMap (pair (natElem a) (vecElem u)) = vecElem (a ::ᵥ u) := by
  apply eq_of_component_eq
  intro j
  cases j with
  | zero =>
    rw [component_push_zero, component_vecElem, dite_eq_left (Nat.succ_pos n)]
    exact congrArg natElem (List.Vector.get_cons_zero a u).symm
  | succ k =>
    rw [component_push_succ, component_vecElem, component_vecElem]
    by_cases hk : k < n
    · rw [dite_eq_left hk, dite_eq_left (show k + 1 < n + 1 by omega)]
      exact congrArg natElem (List.Vector.get_cons_succ a u ⟨k, hk⟩).symm
    · rw [dite_eq_right hk, dite_eq_right (show ¬ k + 1 < n + 1 by omega)]

end DomainTheory.Neighborhood.Theorem56Full
