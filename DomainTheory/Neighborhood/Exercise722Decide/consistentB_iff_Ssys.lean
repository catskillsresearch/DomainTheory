/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise722DFA
import DomainTheory.Neighborhood.Exercise722Cat
import DomainTheory.Neighborhood.Exercise722Words
import DomainTheory.Neighborhood.Exercise722Decide.Basic


namespace DomainTheory.Neighborhood

namespace Exercise722

open scoped Computability
open Sum Set

variable {σ₁ σ₂ : Type}














variable {σ : Type}














/-- **Definition 7.1 (ii) for encoded neighbourhoods:** when `denote a`, `denote b ∈ S`,
`consistentB` agrees with membership of the intersection in `S`. -/
theorem consistentB_iff_Ssys (a b : SExpr) (ha : InS (denote a)) (hb : InS (denote b)) :
    consistentB a b = true ↔ InS (denote a ∩ denote b) := by
  rw [← denote_cap, consistentB_iff]
  exact Iff.symm (Ssys_isPositive (Ssys_mem.mpr ha) (Ssys_mem.mpr hb))

end Exercise722
end DomainTheory.Neighborhood
