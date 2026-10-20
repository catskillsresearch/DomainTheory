/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Data.Finset.Basic
import DomainTheory.InformationSystems.Constructive.Basic


namespace DomainTheory.InformationSystems.Constructive

variable {α : Type*} [DecidableEq α]







/-- The coercion of `u ∪' v` to a `Set` is the (choice-free) set union of the coercions. -/
theorem coe_funion (u v : Finset α) :
    (↑(u ∪' v) : Set α) = (↑u : Set α) ∪ ↑v := by
  ext x
  simp only [Set.mem_union, Finset.mem_coe, mem_funion]

end DomainTheory.InformationSystems.Constructive
