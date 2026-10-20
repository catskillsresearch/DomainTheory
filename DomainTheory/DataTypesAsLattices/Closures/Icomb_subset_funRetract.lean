/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_1

@[expose] public section


namespace DomainTheory.DataTypesAsLattices































/-- **Scott 1976, (5.1).** Every set is below its graph, so `fun` is a closure. -/
theorem Icomb_subset_funRetract : Icomb ⊆ funRetract := by
  intro p hp
  rcases hp with ⟨n, m, rfl, hm⟩
  exact ⟨n, m, rfl, eq_5_1 (e n) hm⟩

end DomainTheory.DataTypesAsLattices
