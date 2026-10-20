/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise118
import Mathlib.Tactic
import DomainTheory.Neighborhood.Exercise127.Basic


namespace DomainTheory.Neighborhood

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)







theorem interUpTo_pairSeq (U W : Set α) :
    V.interUpTo (pairSeq U W) 2 = V.master ∩ U ∩ W := by
  simp only [interUpTo_succ, interUpTo_zero, pairSeq]
  norm_num

end NeighborhoodSystem
end DomainTheory.Neighborhood
