/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Theorem88a
public import DomainTheory.Neighborhood.Definition71
public import DomainTheory.Neighborhood.DAtomDecidable.Basic
public import DomainTheory.Neighborhood.DAtomDecidable.IPos_cons
public import DomainTheory.Neighborhood.DAtomDecidable.meetStep_spec

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)






variable (cons : ℕ → ℕ)




/-- **The meet-fold invariant, folded across a whole list.** Generalizes `meetStep_spec` from one
step to a full list `l`, relative to an arbitrary starting accumulator `init`/set `S`. -/
theorem meetFold_foldl_spec
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m) (l : List ℕ) :
    ∀ {init : ℕ} {S : Set ℕ}, init.unpair.1 ≤ 1 →
      (init.unpair.1 = 1 → idxSet P.X init.unpair.2 = S) → (init.unpair.1 = 0 → S = ∅) →
      (l.foldl (meetStep P cons) init).unpair.1 ≤ 1 ∧
        ((l.foldl (meetStep P cons) init).unpair.1 = 1 →
          idxSet P.X (l.foldl (meetStep P cons) init).unpair.2 = S ∩ IPos P l) ∧
        ((l.foldl (meetStep P cons) init).unpair.1 = 0 → S ∩ IPos P l = ∅) := by
  induction l with
  | nil =>
    intro init S hle h1 h0
    simpa using ⟨hle, h1, h0⟩
  | cons i rest ih =>
    intro init S hle h1 h0
    rw [List.foldl_cons, IPos_cons, ← Set.inter_assoc]
    obtain ⟨hle', h1', h0'⟩ := meetStep_spec P cons hcons hle h1 h0 i
    exact ih hle' h1' h0'

end DomainTheory.Neighborhood
