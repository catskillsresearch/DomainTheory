/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Proposition810b
import DomainTheory.Neighborhood.Table55
import DomainTheory.Neighborhood.Exercise823
import DomainTheory.Neighborhood.Exercise715
import DomainTheory.Neighborhood.Exercise825Pow
import DomainTheory.Neighborhood.Exercise825Embed
import DomainTheory.Neighborhood.Exercise825Closing
import DomainTheory.Neighborhood.Exercise820
import DomainTheory.Neighborhood.Exercise825FixedPoint.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap







theorem isRetraction_cCombinator : IsRetraction cCombinator := by
  show (cInj.comp cProj).comp (cInj.comp cProj) = cInj.comp cProj
  rw [comp_assoc, ← comp_assoc cProj cInj cProj, cProj_comp_cInj, idMap_comp]

end DomainTheory.Neighborhood
