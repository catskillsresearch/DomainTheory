/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem88b
import DomainTheory.Neighborhood.RecursiveCross
import DomainTheory.Neighborhood.Theorem88d.Basic
import DomainTheory.Neighborhood.Theorem88d.primrec_yFoldStep


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)






variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)





















































theorem primrec_yFold : Nat.Primrec (fun t : ℕ => yFold P t.unpair.1 t.unpair.2) :=
  (Nat.Primrec.prec (Nat.Primrec.const (Nat.pair 0 0)) (primrec_yFoldStep P)).of_eq fun _ => rfl

end DomainTheory.Neighborhood
