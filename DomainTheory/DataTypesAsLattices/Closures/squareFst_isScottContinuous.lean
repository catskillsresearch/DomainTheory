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

@[expose] public section


namespace DomainTheory.DataTypesAsLattices































theorem squareFst_isScottContinuous : IsScottContinuous squareFst := by
  intro x
  ext n
  constructor
  · intro hn
    refine mem_scottUnion.mpr ⟨2 ^ (2 * n), ?_, ?_⟩
    · simpa [e_pow2, Set.singleton_subset_iff, squareFst] using hn
    · simp [squareFst, e_pow2]
  · intro hn
    obtain ⟨m, hm, hnm⟩ := mem_scottUnion.mp hn
    exact hm hnm

end DomainTheory.DataTypesAsLattices
