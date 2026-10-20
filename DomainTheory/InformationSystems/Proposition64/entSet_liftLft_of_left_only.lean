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
import DomainTheory.InformationSystems.Proposition64.SumCon_liftSumLeft


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β)

set_option linter.unusedSectionVars false



















namespace ApproximableMap

variable {C : InfoSys γ}









theorem entSet_liftLft_of_left_only {u : Finset (SumToken α β)}
    (hu : SumCon A B u) (hr : rhtFinset u = ∅) :
    (sumSystem A B).EntSet (liftSumLeft (β := β) (lftFinset u)) u := by
  intro p hp
  cases p with
  | bot =>
    exact ⟨SumCon_liftSumLeft A B (lft_mem_Con_of_SumCon_rht_empty A B hu hr), trivial⟩
  | left x =>
    have hx : x ∈ lftFinset u := (mem_lftFinset).2 hp
    refine ⟨SumCon_liftSumLeft A B (lft_mem_Con_of_SumCon_rht_empty A B hu hr), ⟨?_, ?_⟩⟩
    · rw [lftFinset_liftSumLeft]; exact Finset.ne_empty_of_mem hx
    · rw [lftFinset_liftSumLeft]
      exact A.ent_refl (lft_mem_Con_of_SumCon_rht_empty A B hu hr) hx
  | right y =>
    exact False.elim (by
      have : y ∈ rhtFinset u := (mem_rhtFinset).2 hp
      rw [hr] at this
      exact Finset.notMem_empty _ this)

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
