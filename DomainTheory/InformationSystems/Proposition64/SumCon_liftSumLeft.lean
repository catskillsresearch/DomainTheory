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













theorem SumCon_liftSumLeft {v : Finset α} (hv : v ∈ A.Con) :
    SumCon A B (liftSumLeft (β := β) v) :=
  Or.inl ⟨by rw [lftFinset_liftSumLeft]; exact hv, rhtFinset_liftSumLeft (β := β) v⟩

end InfoSys
end DomainTheory.InformationSystems
