/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Theorem88b.Basic
public import DomainTheory.Neighborhood.Theorem88b.eIdx_zero
public import DomainTheory.Neighborhood.Theorem88b.he0
public import DomainTheory.Neighborhood.Theorem88b.hcover
public import DomainTheory.Neighborhood.Theorem88b.genAtom_empty_iff
public import DomainTheory.Neighborhood.RecursiveCross
public import DomainTheory.Neighborhood.Theorem88d.Basic
public import DomainTheory.Neighborhood.Theorem88d.yFold_zero
public import DomainTheory.Neighborhood.Theorem88d.yFold_succ
public import DomainTheory.Neighborhood.Theorem88d.atomUEmpty_zero_or_one
public import DomainTheory.Neighborhood.Theorem88d.yFoldStep_eq

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)






variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)






















































theorem yFold_found_le_one (n : ℕ) : ∀ N, (yFold P n N).unpair.1 ≤ 1 := by
  intro N
  induction N with
  | zero => simp [yFold_zero]
  | succ N ih =>
    rw [yFold_succ, yFoldStep_eq]
    rcases atomUEmpty_zero_or_one P (n + 1) (N + 2 ^ n) with h0 | h1
    · rw [h0, selectFn_zero]
      rcases Nat.eq_zero_or_pos (yFold P n N).unpair.1 with hf0 | hfpos
      · rw [show (yFold P n N).unpair.1 = 0 from hf0, selectFn_zero, unpair_pair_fst]
      · rw [show (yFold P n N).unpair.1 = 1 from by omega, selectFn_one, unpair_pair_fst]
    · rw [h1, selectFn_one]; exact ih

end DomainTheory.Neighborhood
