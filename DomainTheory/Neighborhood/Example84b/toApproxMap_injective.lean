/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Example84
import DomainTheory.Neighborhood.Definition83
import DomainTheory.Neighborhood.Exercise510
import DomainTheory.Neighborhood.Example84b.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}







section Strict



theorem toApproxMap_injective {a b : (funSpace D E).Element} (h : toApproxMap a = toApproxMap b) :
    a = b := by
  rw [← toFilter_toApproxMap a, ← toFilter_toApproxMap b, h]

end Strict
end DomainTheory.Neighborhood
