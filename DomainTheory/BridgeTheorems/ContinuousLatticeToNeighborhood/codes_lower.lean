/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Order.Hom.Basic
import DomainTheory.ContinuousLattice.WayBelow
import DomainTheory.Neighborhood.Basic
import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.Basic


namespace DomainTheory.BridgeTheorems

open DomainTheory.ContinuousLattice
open DomainTheory.Neighborhood
open scoped DomainTheory.ContinuousLattice

namespace ContinuousLatticeToNeighborhood

variable {D : Type*} [CompleteLattice D]















theorem codes_lower (f : Filter (D := D)) {a b : D} (hba : b ≤ a)
    (ha : a ∈ codes f) : b ∈ codes f :=
  f.up_mem ha ⟨b, rfl⟩ (wayBelowUp_anti hba)

end ContinuousLatticeToNeighborhood
end DomainTheory.BridgeTheorems
