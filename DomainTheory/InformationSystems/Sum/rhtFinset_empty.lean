/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.Constructive
import DomainTheory.InformationSystems.Proposition23
import DomainTheory.InformationSystems.Sum.Basic


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]



variable (A : InfoSys α) (B : InfoSys β)












theorem rhtFinset_empty : rhtFinset (∅ : Finset (SumToken α β)) = ∅ := by
  ext y
  constructor
  · intro hy
    exact False.elim (Finset.notMem_empty _ ((mem_rhtFinset).1 hy))
  · intro hy
    exact False.elim (Finset.notMem_empty y hy)

end InfoSys
end DomainTheory.InformationSystems
