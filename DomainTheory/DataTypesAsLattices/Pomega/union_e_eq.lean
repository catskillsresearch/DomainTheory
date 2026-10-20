/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice.Bounded
import Mathlib.Data.Set.Lattice.Disjoint
import DomainTheory.DataTypesAsLattices.Pomega.Basic
import DomainTheory.DataTypesAsLattices.Pomega.e_pow2


namespace DomainTheory.DataTypesAsLattices













theorem union_e_eq (x : Pomega) : (⋃ n, eBelow x n) = x := by
  ext k
  constructor
  · intro hk
    obtain ⟨n, hn, hke⟩ := Set.mem_iUnion.mp hk
    exact hn hke
  · intro hk
    refine Set.mem_iUnion.mpr ⟨2 ^ k, ?_⟩
    simp [eBelow, e_pow2, Set.singleton_subset_iff, hk]

end DomainTheory.DataTypesAsLattices
