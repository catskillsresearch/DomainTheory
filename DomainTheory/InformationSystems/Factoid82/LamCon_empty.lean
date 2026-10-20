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


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]





































variable (A : InfoSys α)



theorem LamCon_empty : LamCon A (∅ : Finset (RawLamToken α)) :=
  ⟨0, by
    change lamAtomFinset ∅ ∈ A.Con ∧ lamFunFinset ∅ = ∅
    rw [lamAtomFinset_empty, lamFunFinset_empty]
    exact ⟨A.con_empty, rfl⟩⟩

end InfoSys
end DomainTheory.InformationSystems
