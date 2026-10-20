/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.Constructive
public import DomainTheory.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.Sum.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]



variable (A : InfoSys α) (B : InfoSys β)












theorem lftFinset_empty : lftFinset (∅ : Finset (SumToken α β)) = ∅ := by
  ext x
  constructor
  · intro hx
    exact False.elim (Finset.notMem_empty _ ((mem_lftFinset).1 hx))
  · intro hx
    exact False.elim (Finset.notMem_empty x hx)

end InfoSys
end DomainTheory.InformationSystems
