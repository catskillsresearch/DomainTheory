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



theorem LamConN_mono {n m : ℕ} (hmn : n ≤ m) {u : Finset (RawLamToken α)}
    (hu : LamConN A n u) : LamConN A m u := by
  induction hmn with
  | refl => exact hu
  | step _ ih => exact Or.inl ih

end InfoSys
end DomainTheory.InformationSystems
