/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.theorem_5_5_iff
import DomainTheory.DataTypesAsLattices.Closures.Vcomb_isRetract
import DomainTheory.DataTypesAsLattices.Closures.Icomb_subset_Vcomb


namespace DomainTheory.DataTypesAsLattices
































/-- **Scott 1976, Theorem 5.5.** `V` itself is a closure, and its fixed
points are exactly the closure operations. -/
theorem theorem_5_5_universe :
    IsClosure Vcomb ∧ ∀ a, IsClosure a ↔ typed a Vcomb :=
  ⟨⟨Icomb_subset_Vcomb, Vcomb_isRetract⟩,
    fun a => (theorem_5_5_iff a).trans ⟨Eq.symm, Eq.symm⟩⟩

end DomainTheory.DataTypesAsLattices
