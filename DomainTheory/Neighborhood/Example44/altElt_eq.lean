/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Example23
import DomainTheory.Neighborhood.Theorem41
import DomainTheory.Neighborhood.Example44.Basic


namespace DomainTheory.Neighborhood.Example44

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap ExampleB






















/-- `a = 0(1a)`: `altElt` satisfies Scott's defining equation. -/
theorem altElt_eq : (consMap false).toElementMap ((consMap true).toElementMap altElt) = altElt := by
  have h := toElementMap_fixElement ((consMap false).comp (consMap true))
  rwa [toElementMap_comp] at h

end DomainTheory.Neighborhood.Example44
