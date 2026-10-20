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
public import DomainTheory.Neighborhood.DAtomDecidable.primrec_meetFoldCode

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)






variable (cons : ℕ → ℕ)









variable (incl : ℕ → ℕ)


theorem primrec_DAtomEmptyChar (hconsp : Nat.Primrec cons) (hinclp : Nat.Primrec incl) :
    Nat.Primrec (fun t => DAtomEmptyChar P cons incl t.unpair.1 t.unpair.2) := by
  have hmf : Nat.Primrec (fun t : ℕ => meetFoldCode P cons t.unpair.1) :=
    (primrec_meetFoldCode P cons hconsp).comp Nat.Primrec.left
  have hmfok : Nat.Primrec (fun t : ℕ => (meetFoldCode P cons t.unpair.1).unpair.1) :=
    Nat.Primrec.left.comp hmf
  have hmfidx : Nat.Primrec (fun t : ℕ => (meetFoldCode P cons t.unpair.1).unpair.2) :=
    Nat.Primrec.right.comp hmf
  have hg : Nat.Primrec (fun s : ℕ => incl (Nat.pair s.unpair.2 s.unpair.1)) :=
    hinclp.comp (Nat.Primrec.right.pair Nat.Primrec.left)
  have hexists : Nat.Primrec
      (fun t : ℕ => existsListChar (fun s => incl (Nat.pair s.unpair.2 s.unpair.1))
        (meetFoldCode P cons t.unpair.1).unpair.2 t.unpair.2) := by
    have hcomb : Nat.Primrec (fun t : ℕ =>
        Nat.pair t.unpair.2 (meetFoldCode P cons t.unpair.1).unpair.2) :=
      Nat.Primrec.right.pair hmfidx
    exact ((primrec_existsListChar hg).comp hcomb).of_eq
      (fun t => by simp only [unpair_pair_fst, unpair_pair_snd])
  exact (primrec_selectFn (primrec_isOne.comp hmfok) hexists (Nat.Primrec.const 1)).of_eq
    (fun _ => rfl)

end DomainTheory.Neighborhood
