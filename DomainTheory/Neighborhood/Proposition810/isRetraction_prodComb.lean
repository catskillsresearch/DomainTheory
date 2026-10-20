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
import DomainTheory.Neighborhood.Proposition810.toElementMap_of_comp_eq_idMap
import DomainTheory.Neighborhood.Proposition810.toElementMap_idem_of_isRetraction
import DomainTheory.Neighborhood.Proposition810.toElementMap_prodComb


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Exercise326


variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}


/-- **Proposition 8.10, `×`-case, retraction half.** -/
theorem isRetraction_prodComb {a b : ApproximableMap U U} (ha : IsRetraction a)
    (hb : IsRetraction b) : IsRetraction (prodComb a b) := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp, toElementMap_prodComb a b ((prodComb a b).toElementMap x),
    toElementMap_prodComb a b x, toElementMap_of_comp_eq_idMap jTimes_comp_iTimes, fst_pair,
    snd_pair, toElementMap_idem_of_isRetraction ha, toElementMap_idem_of_isRetraction hb]

end DomainTheory.Neighborhood
