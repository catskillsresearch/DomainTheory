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


























/-- `zero(0̂) = true`. -/
theorem zeroMap_natElem_zero : zeroMap.toElementMap (natElem 0) = Example23.trueElt :=
  constLiftN_natElem T zeroVal 0

end DomainTheory.Neighborhood.Example43
