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


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β)

set_option linter.unusedSectionVars false



















namespace ApproximableMap

variable {C : InfoSys γ}









theorem entSet_u_of_inl_witness {u u' : Finset (SumToken α β)} {v : Finset α}
    (hlne : lftFinset u ≠ ∅) (hinl : (inlMap A B).rel v u')
    (huv : A.EntSet (lftFinset u) v) (hu : SumCon A B u)
    (hr : rhtFinset u = ∅) :
    (sumSystem A B).EntSet u u' := by
  intro p hp
  have ⟨hv, hu', hr', hEnt⟩ := hinl
  cases p with
  | bot => exact ⟨hu, trivial⟩
  | left x =>
    have hx : x ∈ lftFinset u' := (mem_lftFinset).2 hp
    have hAx : A.Ent v x := hEnt x hx
    have hAx' : A.Ent (lftFinset u) x :=
      A.ent_trans (lft_mem_Con_of_SumCon_rht_empty A B hu hr) hv huv hAx
    exact ⟨hu, ⟨hlne, hAx'⟩⟩
  | right y =>
    exact False.elim (by
      have : y ∈ rhtFinset u' := (mem_rhtFinset).2 hp
      rw [hr'] at this; exact Finset.notMem_empty _ this)

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
