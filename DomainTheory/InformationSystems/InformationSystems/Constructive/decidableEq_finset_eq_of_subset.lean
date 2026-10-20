/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Data.Finset.Basic
import all Mathlib.Data.Finset.Basic
public import DomainTheory.InformationSystems.InformationSystems.Constructive.instLeftCommutativeInsert
public import DomainTheory.InformationSystems.InformationSystems.Constructive.mem_funion
public import DomainTheory.InformationSystems.InformationSystems.Constructive.funion_empty_right
public import DomainTheory.InformationSystems.InformationSystems.Constructive.Basic.notation5

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems.Constructive

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
/-- If mutual subset holds, the finsets are equal. -/
theorem decidableEq_finset_eq_of_subset (s t : Finset α) (h : s ⊆ t ∧ t ⊆ s) : s = t :=
  Finset.Subset.antisymm h.1 h.2

end DomainTheory.InformationSystems.Constructive
