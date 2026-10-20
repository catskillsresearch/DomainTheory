/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise826
import DomainTheory.Neighborhood.Exercise821
import DomainTheory.Neighborhood.Exercise827.Basic
import DomainTheory.Neighborhood.Exercise827.exists_X_of_mem_step


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap






















































/-- **Exercise 8.27(b)(3)(b), assembled over a whole `stepFun` list.** Induction on the list `L`
using `exists_X_of_mem_step` for the head pair and the inductive hypothesis for the tail, combined
via `x.inter_mem` (giving the ambient validity of the intersection "for free", `x.sub`) and
`(piD d).mono`/`.inter_right` (self-relation of an intersection of two self-related nbhds). -/
theorem exists_X_of_mem_stepFun (d : ApproximableMap U U) (x : (funSpace U U).Element)
    (L : List (Set ℚ × Set ℚ)) (hmem : piDApply d (toApproxMap x) ∈ stepFun L) :
    ∃ X, x.mem X ∧ X ⊆ (stepFun L : Set (ApproximableMap U U)) ∧ (piD d).rel X X := by
  induction L with
  | nil =>
    refine ⟨(funSpace U U).master, x.master_mem, ?_, (piD d).master_rel⟩
    simp
  | cons p L ih =>
    rw [stepFun_cons] at hmem
    obtain ⟨hmemP, hmemL⟩ := hmem
    obtain ⟨Xp, hXpx, hXpsub, hXpXp⟩ := exists_X_of_mem_step d x hmemP
    obtain ⟨XL, hXLx, hXLsub, hXLXL⟩ := ih hmemL
    refine ⟨Xp ∩ XL, x.inter_mem hXpx hXLx, ?_, ?_⟩
    · rw [stepFun_cons]
      exact Set.inter_subset_inter hXpsub hXLsub
    · have hvalidP : (funSpace U U).mem Xp := x.sub hXpx
      have hvalidL : (funSpace U U).mem XL := x.sub hXLx
      have hvalidInter : (funSpace U U).mem (Xp ∩ XL) := x.sub (x.inter_mem hXpx hXLx)
      have h1 : (piD d).rel (Xp ∩ XL) Xp :=
        (piD d).mono hXpXp Set.inter_subset_left subset_rfl hvalidInter hvalidP
      have h2 : (piD d).rel (Xp ∩ XL) XL :=
        (piD d).mono hXLXL Set.inter_subset_right subset_rfl hvalidInter hvalidL
      exact (piD d).inter_right h1 h2

end DomainTheory.Neighborhood
