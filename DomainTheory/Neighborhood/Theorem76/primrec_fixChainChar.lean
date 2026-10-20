/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem75
import DomainTheory.Neighborhood.Theorem41
import DomainTheory.Neighborhood.Theorem76.Basic
import DomainTheory.Neighborhood.Theorem76.primrec_fixStp


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}






variable (P : ComputablePresentation V)






theorem primrec_fixChainChar (fincl : ℕ → ℕ) (hfinclp : Nat.Primrec fincl) :
    Nat.Primrec (fun t => fixChainChar P fincl t.unpair.1 t.unpair.2) :=
  (primrec_foldCode (primrec_fixStp fincl hfinclp) Nat.Primrec.left
    (Nat.Primrec.const (Nat.pair P.masterIdx 1)) Nat.Primrec.right).of_eq (fun _ => rfl)

end DomainTheory.Neighborhood
