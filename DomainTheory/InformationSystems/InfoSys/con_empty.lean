/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import DomainTheory.InformationSystems.InfoSys.Basic


namespace DomainTheory.InformationSystems

universe u


namespace InfoSys

variable {α : Type u} [DecidableEq α] (sys : InfoSys α)







/-- Empty set is consistent (subset of any singleton). -/
theorem con_empty : (∅ : Finset α) ∈ sys.Con :=
  sys.con_subset (sys.con_sing sys.bot) (Finset.empty_subset _)

end InfoSys
end DomainTheory.InformationSystems
