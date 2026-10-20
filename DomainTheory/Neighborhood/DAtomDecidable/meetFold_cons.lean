/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem88a
import DomainTheory.Neighborhood.Definition71
import DomainTheory.Neighborhood.DAtomDecidable.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)






variable (cons : ℕ → ℕ)




theorem meetFold_cons (i : ℕ) (rest : List ℕ) :
    meetFold P cons (i :: rest) = (rest.foldl (meetStep P cons) (meetStep P cons
      (Nat.pair 1 P.masterIdx) i)) := by
  unfold meetFold; rw [List.foldl_cons]

end DomainTheory.Neighborhood
