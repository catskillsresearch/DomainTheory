/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise413
import DomainTheory.Neighborhood.Exercise415
import DomainTheory.Neighborhood.Exercise416.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem

variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem



/-- `optimalFix S ⊑ ⋂S`. -/
theorem optimalFix_le_sInf (f : V.Element → V.Element) (hf : Monotone f) (S : Set V.Element)
    (hS : S.Nonempty) (hfix : ∀ s ∈ S, f s = s) :
    optimalFix f hf S hS hfix ≤ V.sInf S hS :=
  monoFix_le f _

end NeighborhoodSystem
end DomainTheory.Neighborhood
