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
public import DomainTheory.Neighborhood.Theorem88d.primrec_stateNeg
public import DomainTheory.Neighborhood.Theorem88d.primrec_atomUCodeState

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)






variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)






theorem primrec_atomUNeg : Nat.Primrec (fun t : ℕ => atomUNeg P t.unpair.1 t.unpair.2) :=
  (primrec_stateNeg.comp (primrec_atomUCodeState P |>.comp
    (Nat.Primrec.right.pair Nat.Primrec.left))).of_eq fun _ => rfl

end DomainTheory.Neighborhood
