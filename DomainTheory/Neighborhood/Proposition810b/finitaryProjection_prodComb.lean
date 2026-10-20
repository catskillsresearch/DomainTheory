/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Proposition810
import DomainTheory.Neighborhood.Theorem86
import DomainTheory.Neighborhood.Proposition810b.Basic
import DomainTheory.Neighborhood.Proposition810b.finitary_prodComb


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Exercise326

universe u v


variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}




variable {a b : ApproximableMap U U}




section ProdCase

variable (a b : ApproximableMap U U)






/-- **Proposition 8.10(b), `×`-case, in full.** `a, b` finitary projections `⟹` `a × b` is a
finitary projection, and its fixed-point set is order-isomorphic to `D_a × D_b`. -/
theorem finitaryProjection_prodComb (ha : IsFinitaryProjection a) (hb : IsFinitaryProjection b) :
    IsFinitaryProjection (prodComb a b) :=
  ⟨isProjection_prodComb ha.1 hb.1, finitary_prodComb a b ha hb⟩

end ProdCase
end DomainTheory.Neighborhood
