/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem86
import DomainTheory.Neighborhood.Theorem41
import DomainTheory.Neighborhood.Exercise315
import DomainTheory.Neighborhood.Exercise816
import DomainTheory.Neighborhood.Exercise823.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Sub8_6

namespace Exercise823

variable {α : Type} {E : NeighborhoodSystem α}


/-- Every approximable map relates every consistent neighbourhood to the master (widen the master
relation's input down to `X` using `mono`, since `X ⊆ Δ` always). -/
theorem rel_master_of_mem (f : ApproximableMap E E) {X : Set α} (hX : E.mem X) :
    f.rel X E.master :=
  f.mono f.master_rel (E.sub_master hX) subset_rfl hX E.master_mem

end Exercise823
end DomainTheory.Neighborhood
