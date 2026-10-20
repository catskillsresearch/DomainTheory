/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Approximable
import DomainTheory.Neighborhood.Example12
import DomainTheory.Neighborhood.Exercise412.Basic


namespace DomainTheory.Neighborhood.Exercise412

open NeighborhoodSystem ApproximableMap Example12 Example12.neighborhoodSystem





/-- **Exercise 4.12 (Scott 1981, PRG-19).** Every element is a fixed point of the identity map
(so `I_T` has *many* fixed points: `⊥`, `elemZero`, `elemOne`). -/
theorem idMap_fixed (x : T.Element) : (idMap T).toElementMap x = x := toElementMap_idMap x

end DomainTheory.Neighborhood.Exercise412
