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
import DomainTheory.InformationSystems.Factoid82.LamEntN_con


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]





































variable (A : InfoSys α)




















theorem LamEnt_con {u : Finset (RawLamToken α)} {t : RawLamToken α}
    (ht : LamEnt A u t) : LamCon A u := by
  rcases ht with ⟨n, ht⟩
  exact ⟨n, LamEntN_con A ht⟩

end InfoSys
end DomainTheory.InformationSystems
