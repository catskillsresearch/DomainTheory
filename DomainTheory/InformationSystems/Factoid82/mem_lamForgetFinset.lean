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












theorem mem_lamForgetFinset {u : Finset (LamToken A)} {t : RawLamToken α} :
    t ∈ lamForgetFinset A u ↔ ∃ p ∈ u, p.val = t := by
  simpa [lamForgetFinset] using mem_foldr_lamForget A u.1 t

end InfoSys
end DomainTheory.InformationSystems
