/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.FunctionSpace
import DomainTheory.InformationSystems.Sum
import Mathlib.Data.Finset.Card
import DomainTheory.InformationSystems.Factoid82.Basic
import DomainTheory.InformationSystems.Factoid82.LamCon_subset
import DomainTheory.InformationSystems.Factoid82.mem_lamForgetFinset


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]





































variable (A : InfoSys α)

















theorem LamTokenCon_subset {u v : Finset (LamToken A)}
    (hu : LamTokenCon A u) (hv : v ⊆ u) : LamTokenCon A v :=
  LamCon_subset A hu (by
    intro t ht
    rcases (mem_lamForgetFinset A).1 ht with ⟨p, hp, rfl⟩
    exact (mem_lamForgetFinset A).2 ⟨p, hv hp, rfl⟩)

end InfoSys
end DomainTheory.InformationSystems
