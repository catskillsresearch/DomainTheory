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
public import DomainTheory.Neighborhood.DAtomDecidable.primrec_meetStepCode

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)






variable (cons : ℕ → ℕ)








theorem primrec_meetFoldCode (hconsp : Nat.Primrec cons) :
    Nat.Primrec (meetFoldCode P cons) :=
  (primrec_foldCode (primrec_meetStepCode P cons hconsp) (Nat.Primrec.const 0)
    (Nat.Primrec.const (Nat.pair 1 P.masterIdx)) primrec_id).of_eq (fun _ => rfl)

end DomainTheory.Neighborhood
