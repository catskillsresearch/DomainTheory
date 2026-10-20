/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.UComputablePresentation
import DomainTheory.Neighborhood.SplitU.Basic


namespace DomainTheory.Neighborhood

open Domain.Recursive NeighborhoodSystem







theorem primrec_clipGeCode : Nat.Primrec clipGeCode := by
  have hm : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
  have he1 : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have he2 : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  exact (Nat.Primrec.pair (primrec_ratMaxCode.comp (he1.pair hm)) he2).of_eq
    fun t => by simp only [clipGeCode]

end DomainTheory.Neighborhood
