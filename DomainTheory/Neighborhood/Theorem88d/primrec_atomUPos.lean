/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem88b
import DomainTheory.Neighborhood.RecursiveCross
import DomainTheory.Neighborhood.Theorem88d.Basic
import DomainTheory.Neighborhood.Theorem88d.primrec_statePos
import DomainTheory.Neighborhood.Theorem88d.primrec_atomUCodeState


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)






variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)






theorem primrec_atomUPos : Nat.Primrec (fun t : ℕ => atomUPos P t.unpair.1 t.unpair.2) :=
  (primrec_statePos.comp (primrec_atomUCodeState P |>.comp
    (Nat.Primrec.right.pair Nat.Primrec.left))).of_eq fun _ => rfl

end DomainTheory.Neighborhood
