/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise516
import Mathlib.Data.Nat.Bits
import DomainTheory.Neighborhood.Exercise516ThueMorse.Basic
import DomainTheory.Neighborhood.Exercise516ThueMorse.tmOp_strBot
import DomainTheory.Neighborhood.Exercise516ThueMorse.tmOp_strBot_expand
import DomainTheory.Neighborhood.Exercise516ThueMorse.iterElem_zerou27
import DomainTheory.Neighborhood.Exercise516ThueMorse.iterElem_succ
import DomainTheory.Neighborhood.Exercise516ThueMorse.iterate_expand_cons
import DomainTheory.Neighborhood.Exercise516ThueMorse.strBot_nil


namespace DomainTheory.Neighborhood.Exercise516

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419








/-- **Exercise 5.16 (the approximants).** The `(k+1)`-st approximant of the least fixed point is the
partial element of the `k`-fold Thue–Morse morphism iterate of `[0]`:
`Φᵏ⁺¹(⊥) = (expandᵏ[0])⊥`. -/
theorem iterElem_succ_eq (k : ℕ) :
    tmOp.iterElem (k + 1) = strBot (expand^[k] [false]) := by
  induction k with
  | zero =>
    rw [iterElem_succ, iterElem_zero', ← strBot_nil, tmOp_strBot]
    rfl
  | succ k ih =>
    obtain ⟨ρ, hρ⟩ := iterate_expand_cons k
    rw [iterElem_succ, ih, hρ, tmOp_strBot_expand, ← hρ, Function.iterate_succ_apply']

end DomainTheory.Neighborhood.Exercise516
