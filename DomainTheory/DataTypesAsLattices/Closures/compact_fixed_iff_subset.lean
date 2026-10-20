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
import DomainTheory.DataTypesAsLattices.Closures.closureCompact_isCompactSubset


namespace DomainTheory.DataTypesAsLattices


















theorem compact_fixed_iff_subset {a : Pomega} (ha : IsClosure a)
    (x : Fixpoints (funOf a)) :
    IsCompactSubset x ↔ ∃ n, x = closureCompact a ha n := by
  constructor
  · intro hx
    obtain ⟨y, hy, hxy⟩ :=
      hx (compactFixedBelow a x) (compactFixedBelow_directedSubset ha x)
        (le_of_eq (compactFixedBelow_sUnion ha x))
    obtain ⟨⟨n, hn⟩, hyx⟩ := hy
    have hyx' : (y : Pomega) ⊆ x := hyx
    have : y = x := Subtype.ext (subset_antisymm hyx' hxy)
    refine ⟨n, this.symm.trans (Subtype.ext hn)⟩
  · rintro ⟨n, rfl⟩
    exact closureCompact_isCompactSubset ha n

end DomainTheory.DataTypesAsLattices
