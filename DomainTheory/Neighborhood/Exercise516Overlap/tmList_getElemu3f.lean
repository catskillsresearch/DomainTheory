/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise516ThueMorse
import DomainTheory.Neighborhood.Exercise516Overlap.Basic


namespace DomainTheory.Neighborhood.Exercise516

open DomainTheory.Neighborhood






open Example44 ExampleB NeighborhoodSystem

/-- The `j`-th bit of the length-`n` Thue–Morse prefix is `tm j`. -/
theorem tmList_getElem? {n j : ℕ} (h : j < n) : (tmList n)[j]? = some (tm j) := by
  rw [tmList, List.getElem?_map, List.getElem?_range h]
  rfl

end DomainTheory.Neighborhood.Exercise516
