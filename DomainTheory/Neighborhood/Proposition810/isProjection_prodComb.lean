/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Definition89
import DomainTheory.Neighborhood.Definition83
import DomainTheory.Neighborhood.Theorem69
import DomainTheory.Neighborhood.Proposition810.Basic
import DomainTheory.Neighborhood.Proposition810.isRetraction_prodComb
import DomainTheory.Neighborhood.Proposition810.le_idMap_prodComb


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Exercise326


variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}


/-- **Proposition 8.10 (Scott 1981, PRG-19), `×`-case.** `a, b` projections `⟹` `a × b` a
projection. -/
theorem isProjection_prodComb {a b : ApproximableMap U U}
    (ha : IsProjection a) (hb : IsProjection b) : IsProjection (prodComb a b) :=
  ⟨isRetraction_prodComb ha.1 hb.1, le_idMap_prodComb ha.2 hb.2⟩

end DomainTheory.Neighborhood
