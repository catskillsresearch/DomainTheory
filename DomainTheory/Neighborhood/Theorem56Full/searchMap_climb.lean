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
import DomainTheory.Neighborhood.Theorem56Full.searchMap_step_found
import DomainTheory.Neighborhood.Theorem56Full.searchMap_step_next


namespace DomainTheory.Neighborhood.Theorem56Full

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap
open DomainTheory.Neighborhood.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.Neighborhood.Exercise326 (cond)
open DomainTheory.Neighborhood.Exercise511 (head tail push)
























section Rfind

variable (φf : ApproximableMap 𝒩 N)





/-- **Capstone (least zero ⟹ value).** If `m` is a zero of `f(· ::ᵥ v)` and nothing below it is, then
starting from any counter `j ≤ m` the search returns `m`. (Downward induction on `m - j`.) -/
theorem searchMap_climb {n : ℕ} {f : List.Vector ℕ (n + 1) → ℕ}
    (hf : LamDef φf (f : List.Vector ℕ (n + 1) →. ℕ)) (v : List.Vector ℕ n) (m : ℕ)
    (hm0 : f (m ::ᵥ v) = 0) (hmin : ∀ i, i < m → f (i ::ᵥ v) ≠ 0) :
    ∀ d j, j + d = m → (searchMap φf).toElementMap (vecElem (j ::ᵥ v)) = natElem m := by
  intro d
  induction d with
  | zero =>
    intro j hj
    have hjm : j = m := by omega
    rw [hjm]
    exact searchMap_step_found φf hf v m hm0
  | succ d ih =>
    intro j hj
    have hjm : j < m := by omega
    rw [searchMap_step_next φf hf v j (hmin j hjm)]
    exact ih (j + 1) (by omega)

end Rfind
end DomainTheory.Neighborhood.Theorem56Full
