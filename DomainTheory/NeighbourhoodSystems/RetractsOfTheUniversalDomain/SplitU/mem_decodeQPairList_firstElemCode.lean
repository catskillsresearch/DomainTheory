/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem












theorem mem_decodeQPairList_firstElemCode {c : ℕ} (hc : c ≠ 0) :
    decodeRatPair (firstElemCode c) ∈ decodeQPairList c := by
  obtain ⟨c', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hc
  have : firstElemCode (c' + 1) = c'.unpair.1 := by unfold firstElemCode; simp
  unfold decodeQPairList
  rw [this, decodeList_succ]
  exact List.mem_map_of_mem (by simp)

end DomainTheory.NeighbourhoodSystems
