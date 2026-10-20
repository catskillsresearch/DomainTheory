/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.UComputablePresentation
import DomainTheory.Neighborhood.SplitU.Basic
import DomainTheory.Neighborhood.SplitU.primrec_clipLtCode


namespace DomainTheory.Neighborhood

open Domain.Recursive NeighborhoodSystem










theorem primrec_clipLtListCode : Nat.Primrec (fun t : ℕ => clipLtListCode t.unpair.1 t.unpair.2) := by
  have hg : Nat.Primrec (fun t : ℕ => Nat.pair (clipLtCode t) 0 + 1) :=
    Nat.Primrec.succ.comp (primrec_clipLtCode.pair (Nat.Primrec.const 0))
  exact (primrec_flatMapCode hg).of_eq fun _ => rfl

end DomainTheory.Neighborhood
