/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Definition71
import DomainTheory.Neighborhood.Approximable
import DomainTheory.Neighborhood.Definition72.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}



variable {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}

/-- **The identity map is computable** (the identity half of Proposition 7.3). The relation
`Xₙ I Xₘ` is `Xₙ ⊆ Xₘ` (`incl_computable`), which is recursively *decidable*, hence recursively
enumerable. -/
theorem idMap_isComputable (P : ComputablePresentation V) :
    IsComputableMap P P (idMap V) :=
  (RecDecidable.of_iff (fun t => by
    simp only [idMap_rel]
    exact ⟨fun h => h.2.2, fun h => ⟨P.mem_X _, P.mem_X _, h⟩⟩)
    P.incl_computable).re

end DomainTheory.Neighborhood
