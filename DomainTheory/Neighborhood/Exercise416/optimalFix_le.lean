/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise413
import DomainTheory.Neighborhood.Exercise415
import DomainTheory.Neighborhood.Exercise416.Basic
import DomainTheory.Neighborhood.Exercise416.optimalFix_le_sInf


namespace DomainTheory.Neighborhood

open NeighborhoodSystem

variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem



/-- **Exercise 4.16 (Scott 1981, PRG-19).** `optimalFix S` lies below every member of `S`. -/
theorem optimalFix_le (f : V.Element → V.Element) (hf : Monotone f) (S : Set V.Element)
    (hS : S.Nonempty) (hfix : ∀ s ∈ S, f s = s) {s : V.Element} (hs : s ∈ S) :
    optimalFix f hf S hS hfix ≤ s :=
  le_trans (optimalFix_le_sInf f hf S hS hfix) (V.sInf_le S hS hs)

end NeighborhoodSystem
end DomainTheory.Neighborhood
