/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise722Decide
import DomainTheory.Neighborhood.Exercise722Equiv.Basic
import DomainTheory.Neighborhood.Exercise722Equiv.subsetB_iff


namespace DomainTheory.Neighborhood

namespace Exercise722

open scoped Computability
open Sum Set













theorem interEqB_iff (e1 e2 : SExpr) : interEqB e1 e2 = true ↔ denote e1 = denote e2 := by
  unfold interEqB
  rw [Bool.and_eq_true, subsetB_iff, subsetB_iff, ← Set.Subset.antisymm_iff]

end Exercise722
end DomainTheory.Neighborhood
