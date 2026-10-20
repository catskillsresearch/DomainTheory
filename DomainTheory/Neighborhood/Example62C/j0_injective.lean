/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Example62
import DomainTheory.Neighborhood.Example44
import DomainTheory.Neighborhood.Exercise315
import DomainTheory.Neighborhood.Example62C.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62








variable {α β γ : Type*}

























theorem j0_injective {X X' : Set α}
    (h : (j0 X : Set (Option (α ⊕ β ⊕ γ))) = j0 X') : X = X' :=
  Set.Subset.antisymm (j0_subset_j0.mp h.subset) (j0_subset_j0.mp h.symm.subset)

end DomainTheory.Neighborhood
