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
public import DomainTheory.InformationSystems.InformationSystems.Constructive.Basic.notation5

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems.Constructive

variable {α : Type*} [DecidableEq α]

theorem mem_foldr_insert (a : α) (u : Finset α) (s : Multiset α) :
    a ∈ Multiset.foldr insert u s ↔ a ∈ u ∨ a ∈ s := by
  refine Multiset.induction_on s ?_ ?_
  · simp
  · intro b t ih
    simp only [Multiset.foldr_cons, Finset.mem_insert, ih, Multiset.mem_cons]
    constructor
    · rintro (h | h | h)
      exacts [Or.inr (Or.inl h), Or.inl h, Or.inr (Or.inr h)]
    · rintro (h | h | h)
      exacts [Or.inr (Or.inl h), Or.inl h, Or.inr (Or.inr h)]

end DomainTheory.InformationSystems.Constructive
