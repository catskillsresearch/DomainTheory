/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.valStage_subset
public import DomainTheory.DataTypesAsLattices.Enumeration.valStage_eq_of_rank_le

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices



































/-- `valC` and the well-founded numerical evaluator denote the same
enumeration on integer arguments. -/
theorem valC_valNat (n : ℕ) : funOf valC (ofNat n) = valNat n := by
  rw [valC, fix, funOf_iUnion]
  apply subset_antisymm
  · intro k hk
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hk
    exact valStage_subset s n hs
  · intro k hk
    exact Set.mem_iUnion.mpr
      ⟨valRank n, (valStage_eq_of_rank_le n (valRank n) le_rfl).symm ▸ hk⟩

end DomainTheory.DataTypesAsLattices
