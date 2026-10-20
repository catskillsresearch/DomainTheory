/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.FunctionSpace
import DomainTheory.Neighborhood.Definition72
import DomainTheory.Neighborhood.Theorem74
import DomainTheory.Neighborhood.Theorem75.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}






theorem interList_subset_base {base : Set β} {M : List (Set β)} : interList base M ⊆ base :=
  fun _ hz => (mem_interList.mp hz).1

end DomainTheory.Neighborhood
