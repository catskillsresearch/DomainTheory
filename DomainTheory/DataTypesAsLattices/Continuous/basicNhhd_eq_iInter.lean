/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Topology.Bases
import Mathlib.Topology.Order
import DomainTheory.DataTypesAsLattices.Pomega
import DomainTheory.DataTypesAsLattices.Continuous.Basic


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace








/-- A basic neighbourhood is a finite intersection of subbasic opens. -/
theorem basicNhhd_eq_iInter (n : ℕ) :
    basicNhhd n = ⋂ k ∈ e n, memOpen k := by
  ext x
  simp [basicNhhd, memOpen, Set.subset_def]

end DomainTheory.DataTypesAsLattices
