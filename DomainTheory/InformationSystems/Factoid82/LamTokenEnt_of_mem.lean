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
import DomainTheory.InformationSystems.Factoid82.mem_lamForgetFinset
import DomainTheory.InformationSystems.Factoid82.LamEnt_of_mem


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]





































variable (A : InfoSys α)






















theorem LamTokenEnt_of_mem {u : Finset (LamToken A)} {p : LamToken A}
    (hu : LamTokenCon A u) (hp : p ∈ u) : LamTokenEnt A u p :=
  LamEnt_of_mem A hu ((mem_lamForgetFinset A).2 ⟨p, hp, rfl⟩)

end InfoSys
end DomainTheory.InformationSystems
