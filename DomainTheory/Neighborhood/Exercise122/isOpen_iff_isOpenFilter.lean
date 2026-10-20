/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Basic
import Mathlib.Topology.Inseparable
import DomainTheory.Neighborhood.Exercise122.Basic


namespace DomainTheory.Neighborhood

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)







/-- `IsOpen` for `|𝒟|` is exactly Scott's condition (ii). -/
theorem isOpen_iff_isOpenFilter (U : Set V.Element) : IsOpen U ↔ V.IsOpenFilter U := Iff.rfl

end NeighborhoodSystem
end DomainTheory.Neighborhood
