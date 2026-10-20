/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.compactFixedBelow_directedSubset
import DomainTheory.DataTypesAsLattices.Closures.compactFixedBelow_sUnion
import DomainTheory.DataTypesAsLattices.Closures.compact_fixed_iff_subset


namespace DomainTheory.DataTypesAsLattices


















/-- **Scott 1976, Theorem 5.1 (The algebraic lattice theorem).**
The compact points of a closure range are exactly the `a(e n)`, and every
fixed point is their directed supremum. -/
theorem theorem_5_1 {a : Pomega} (ha : IsClosure a) :
    (∀ x : Fixpoints (funOf a),
      IsCompactSubset x ↔ ∃ n, x = closureCompact a ha n) ∧
    ∀ x : Fixpoints (funOf a),
      IsDirectedSubset (compactFixedBelow a x) ∧
        (x : Pomega) = ⋃₀ (Subtype.val '' compactFixedBelow a x) :=
  ⟨compact_fixed_iff_subset ha, fun x =>
    ⟨compactFixedBelow_directedSubset ha x, compactFixedBelow_sUnion ha x⟩⟩

end DomainTheory.DataTypesAsLattices
