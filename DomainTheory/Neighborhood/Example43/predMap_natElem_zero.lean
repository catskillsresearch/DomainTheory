/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Example23
import DomainTheory.Neighborhood.Theorem41
import DomainTheory.Neighborhood.Example43.Basic
import DomainTheory.Neighborhood.Example43.constLiftN_natElem


namespace DomainTheory.Neighborhood.Example43

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap






















/-- `pred(0̂) = ⊥`: predecessor of zero is undefined. -/
theorem predMap_natElem_zero : predMap.toElementMap (natElem 0) = N.bot :=
  constLiftN_natElem N predVal 0

end DomainTheory.Neighborhood.Example43
