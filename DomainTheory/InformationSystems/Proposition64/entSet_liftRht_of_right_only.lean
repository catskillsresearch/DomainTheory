/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.Sum
import DomainTheory.InformationSystems.Factoid33
import DomainTheory.InformationSystems.Proposition53
import DomainTheory.InformationSystems.Proposition55
import DomainTheory.InformationSystems.Proposition64.Basic
import DomainTheory.InformationSystems.Proposition64.SumCon_liftSumRight


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β)

set_option linter.unusedSectionVars false



















namespace ApproximableMap

variable {C : InfoSys γ}









theorem entSet_liftRht_of_right_only {u : Finset (SumToken α β)}
    (hu : SumCon A B u) (hl : lftFinset u = ∅) :
    (sumSystem A B).EntSet (liftSumRight (α := α) (rhtFinset u)) u := by
  intro p hp
  cases p with
  | bot =>
    exact ⟨SumCon_liftSumRight A B (rht_mem_Con_of_SumCon_lft_empty A B hu hl), trivial⟩
  | right y =>
    have hy : y ∈ rhtFinset u := (mem_rhtFinset).2 hp
    refine ⟨SumCon_liftSumRight A B (rht_mem_Con_of_SumCon_lft_empty A B hu hl), ⟨?_, ?_⟩⟩
    · rw [rhtFinset_liftSumRight]; exact Finset.ne_empty_of_mem hy
    · rw [rhtFinset_liftSumRight]
      exact B.ent_refl (rht_mem_Con_of_SumCon_lft_empty A B hu hl) hy
  | left x =>
    exact False.elim (by
      have : x ∈ lftFinset u := (mem_lftFinset).2 hp
      rw [hl] at this
      exact Finset.notMem_empty _ this)

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
