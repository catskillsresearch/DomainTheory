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
public import DomainTheory.InformationSystems.InformationSystems.Constructive.decidableEq_finset_eq_of_subset
public import DomainTheory.InformationSystems.InformationSystems.Constructive.decidableEq_finset_false_of_ne
public import DomainTheory.InformationSystems.InformationSystems.Constructive.Basic.notation5

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems.Constructive

variable {α : Type*} [DecidableEq α]

/-- Choice-free decidable equality for `Finset`.
mathlib's `Finset.decidableEq` goes through `Multiset` quotients and pulls
`Classical.choice`; this version uses only decidable membership and subset. -/
def decidableEq_finset {α : Type*} [DecidableEq α] : DecidableEq (Finset α) :=
  fun s t =>
    if h : s ⊆ t ∧ t ⊆ s then
      isTrue (decidableEq_finset_eq_of_subset s t h)
    else
      isFalse (decidableEq_finset_false_of_ne s t h)

end DomainTheory.InformationSystems.Constructive
