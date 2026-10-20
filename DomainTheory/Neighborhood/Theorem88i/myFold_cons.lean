/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem88h
import DomainTheory.Neighborhood.Theorem88i.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)





theorem myFold_cons (e : ℕ) (rest : List ℕ) :
    myFold P qChar cons (e :: rest) = rest.foldl (myStep P qChar cons) (myStep P qChar cons P.masterIdx e) := by
  unfold myFold; rw [List.foldl_cons]

end DomainTheory.Neighborhood
