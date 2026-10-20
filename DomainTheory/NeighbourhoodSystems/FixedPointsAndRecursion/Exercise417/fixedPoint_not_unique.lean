/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise414
public import Mathlib.Algebra.Group.Submonoid.Basic
import all Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
import all Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Nat.Defs
import all Mathlib.Algebra.Group.Nat.Defs
public import DomainTheory.Neighborhood.Exercise417.Basic
public import DomainTheory.Neighborhood.Exercise417.F_univ
public import DomainTheory.Neighborhood.Exercise417.F_one_one_singleton

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise417

open Pointwise
open DomainTheory.Neighborhood.Exercise414

variable {S : Type*} [Monoid S]








/-- **Exercise 4.17 (Scott 1981, PRG-19).** The fixed point need **not** be unique: over `S = ℕ`
(under `·`) with `a = b = 1`, both `{1}` (the least solution) and `Set.univ` solve the equation, and
they are distinct. -/
theorem fixedPoint_not_unique :
    ∃ x y : Set ℕ, F 1 1 x = x ∧ F 1 1 y = y ∧ x ≠ y := by
  refine ⟨{1}, Set.univ, F_one_one_singleton, F_univ 1 1, ?_⟩
  intro h
  have h2 : (2 : ℕ) ∈ ({1} : Set ℕ) := by rw [h]; exact Set.mem_univ 2
  simp at h2

end DomainTheory.Neighborhood.Exercise417
