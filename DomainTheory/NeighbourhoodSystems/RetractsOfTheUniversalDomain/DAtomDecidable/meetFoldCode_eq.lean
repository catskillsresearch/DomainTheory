/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Theorem88a.Basic
public import DomainTheory.Neighborhood.Theorem88a.idxSet_nonempty
public import DomainTheory.Neighborhood.Theorem88a.idxSet_eq_iff
public import DomainTheory.Neighborhood.Theorem88a.isomorphic_DprimeU
public import DomainTheory.Neighborhood.Theorem88a.theorem_8_8_a
public import DomainTheory.Neighborhood.Theorem88a.theorem_8_8
public import DomainTheory.Neighborhood.Definition71
public import DomainTheory.Neighborhood.DAtomDecidable.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)






variable (cons : ℕ → ℕ)








theorem meetFoldCode_eq (c : ℕ) : meetFoldCode P cons c = meetFold P cons (decodeList c) := by
  have hfun : (fun (acc x : ℕ) => meetStepCode P cons (Nat.pair x (Nat.pair acc 0)))
      = meetStep P cons := by
    funext acc x
    unfold meetStepCode
    simp only [unpair_pair_fst, unpair_pair_snd]
  unfold meetFoldCode meetFold
  rw [foldCode_eq', hfun]

end DomainTheory.Neighborhood
