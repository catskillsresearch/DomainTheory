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









theorem eq_botElement_of_no_injections (z : (sumSystem A B).Element)
    (hL : ∀ x : α, SumToken.left x ∉ z.carrier)
    (hR : ∀ y : β, SumToken.right y ∉ z.carrier) :
    z = (sumSystem A B).botElement := by
  apply le_antisymm
  · intro p hp
    cases p with
    | bot =>
      change SumToken.bot ∈ (sumSystem A B).botElement.carrier
      exact (sumSystem A B).ent_refl ((sumSystem A B).con_sing _) (Finset.mem_singleton_self _)
    | left x => exact False.elim (hL x hp)
    | right y => exact False.elim (hR y hp)
  · exact botElement_le (sumSystem A B) z

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
