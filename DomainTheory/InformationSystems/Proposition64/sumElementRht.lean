/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.Sum
public import DomainTheory.InformationSystems.Factoid33
public import DomainTheory.InformationSystems.Proposition53
public import DomainTheory.InformationSystems.Proposition55
public import DomainTheory.InformationSystems.Proposition64.instLeftCommutativeLiftSumLeft
public import DomainTheory.InformationSystems.Proposition64.instLeftCommutativeLiftSumRight
public import DomainTheory.InformationSystems.Proposition64.liftSumRight
public import DomainTheory.InformationSystems.Proposition64.mem_liftSumRight
public import DomainTheory.InformationSystems.Proposition64.rhtFinset_liftSumRight
public import DomainTheory.InformationSystems.Proposition64.lftFinset_liftSumRight
public import DomainTheory.InformationSystems.Proposition64.rht_mem_Con_of_SumCon_lft_empty
public import DomainTheory.InformationSystems.Proposition64.sumRhtCarrier

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β)

set_option linter.unusedSectionVars false

namespace ApproximableMap

variable {C : InfoSys γ}

/-- Right copy as a `B`-element, given some right token in `z`. -/
def sumElementRht (z : (sumSystem A B).Element)
    (y0 : β) (hy0 : SumToken.right y0 ∈ z.carrier) : B.Element where
  carrier := sumRhtCarrier A B z
  consistent := by
    intro W hW
    have hsub : (↑(liftSumRight (α := α) W) : Set _) ⊆ z.carrier := by
      intro p hp
      rcases (mem_liftSumRight (α := α)).1 (Finset.mem_coe.1 hp) with ⟨y, hy, rfl⟩
      exact hW (Finset.mem_coe.2 hy)
    have h := rht_mem_Con_of_SumCon_lft_empty A B (z.consistent _ hsub)
      (lftFinset_liftSumRight (α := α) W)
    rwa [rhtFinset_liftSumRight] at h
  closed := by
    intro W b hW hEnt
    if hempty : W = ∅ then
      subst hempty
      have hEnt' : B.Ent {y0} b :=
        B.ent_trans (B.con_sing y0) B.con_empty
          (fun _ h => False.elim (Finset.notMem_empty _ h)) hEnt
      have hsub : (↑({SumToken.right y0} : Finset (SumToken α β)) : Set _) ⊆ z.carrier := by
        intro p hp
        have : p = .right y0 := Finset.mem_singleton.mp (Finset.mem_coe.1 hp)
        subst this; exact hy0
      have hSum : (sumSystem A B).Ent {SumToken.right y0} (.right b) := by
        refine ⟨z.consistent _ hsub, ⟨Finset.singleton_ne_empty _, ?_⟩⟩
        rw [rhtFinset_singleton_right]; exact hEnt'
      exact z.closed _ _ hsub hSum
    else
      have hsub : (↑(liftSumRight (α := α) W) : Set _) ⊆ z.carrier := by
        intro p hp
        rcases (mem_liftSumRight (α := α)).1 (Finset.mem_coe.1 hp) with ⟨y, hy, rfl⟩
        exact hW (Finset.mem_coe.2 hy)
      have hSum : (sumSystem A B).Ent (liftSumRight (α := α) W) (.right b) := by
        refine ⟨z.consistent _ hsub, ⟨?_, ?_⟩⟩
        · rw [rhtFinset_liftSumRight]; exact hempty
        · rw [rhtFinset_liftSumRight]; exact hEnt
      exact z.closed _ _ hsub hSum

end ApproximableMap

end InfoSys

end DomainTheory.InformationSystems
