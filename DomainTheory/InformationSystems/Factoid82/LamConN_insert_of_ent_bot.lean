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
import DomainTheory.InformationSystems.Factoid82.LamConN_insert_bot


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]





































variable (A : InfoSys α)



























theorem LamConN_insert_of_ent_bot {n : ℕ} {u : Finset (RawLamToken α)}
    (ht : LamEntN A n u .bot) : LamConN A n (insert (.bot : RawLamToken α) u) :=
  LamConN_insert_bot A (LamEntN_con A ht)

end InfoSys
end DomainTheory.InformationSystems
