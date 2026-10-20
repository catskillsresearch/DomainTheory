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



















/-- `succ(n̂) = (n+1)^`. -/
theorem succMap_natElem (n : ℕ) : succMap.toElementMap (natElem n) = natElem (n + 1) :=
  constLiftN_natElem N (fun n => natElem (n + 1)) n

end DomainTheory.Neighborhood.Example43
