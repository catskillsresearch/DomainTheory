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












theorem mem_codes_iff {f : Filter (D := D)} {a : D} :
    a ∈ codes f ↔ f.mem (wayBelowUp a) :=
  Iff.rfl

end ContinuousLatticeToNeighborhood
end DomainTheory.BridgeTheorems
