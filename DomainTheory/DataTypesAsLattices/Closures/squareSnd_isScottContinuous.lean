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































theorem squareSnd_isScottContinuous : IsScottContinuous squareSnd := by
  intro x
  ext m
  constructor
  · intro hm
    refine mem_scottUnion.mpr ⟨2 ^ (2 * m + 1), ?_, ?_⟩
    · simpa [e_pow2, Set.singleton_subset_iff, squareSnd] using hm
    · simp [squareSnd, e_pow2]
  · intro hm
    obtain ⟨k, hk, hkm⟩ := mem_scottUnion.mp hm
    exact hk hkm

end DomainTheory.DataTypesAsLattices
