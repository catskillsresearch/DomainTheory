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
import DomainTheory.InformationSystems.Factoid82.LamEntN_of_mem


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]





































variable (A : InfoSys α)





















theorem LamEnt_of_mem {u : Finset (RawLamToken α)} {t : RawLamToken α}
    (hu : LamCon A u) (ht : t ∈ u) : LamEnt A u t := by
  rcases hu with ⟨n, hu⟩
  exact ⟨n, LamEntN_of_mem A hu ht⟩

end InfoSys
end DomainTheory.InformationSystems
