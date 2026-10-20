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
import DomainTheory.InformationSystems.Factoid82.LamCon_empty
import DomainTheory.InformationSystems.Factoid82.lamForgetFinset_empty


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]





































variable (A : InfoSys α)

















theorem LamTokenCon_empty : LamTokenCon A (∅ : Finset (LamToken A)) := by
  simpa [LamTokenCon, lamForgetFinset_empty] using LamCon_empty A

end InfoSys
end DomainTheory.InformationSystems
