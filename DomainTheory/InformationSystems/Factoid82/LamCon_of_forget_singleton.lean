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
import DomainTheory.InformationSystems.Factoid82.LamCon_singleton_bot
import DomainTheory.InformationSystems.Factoid82.LamCon_singleton_atom
import DomainTheory.InformationSystems.Factoid82.lamForgetFinset_singleton
import DomainTheory.InformationSystems.Factoid82.LamCon_singleton_funTok


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]





































variable (A : InfoSys α)
















theorem LamCon_of_forget_singleton (p : LamToken A) :
    LamCon A (lamForgetFinset A {p}) := by
  rw [lamForgetFinset_singleton]
  match p with
  | ⟨.bot, _⟩ => exact LamCon_singleton_bot A
  | ⟨.atom x, _⟩ => exact LamCon_singleton_atom A x
  | ⟨.funTok u v, hWF⟩ => exact LamCon_singleton_funTok A u v hWF.1 hWF.2

end InfoSys
end DomainTheory.InformationSystems
