/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Proposition810
import DomainTheory.Neighborhood.Theorem86
import DomainTheory.Neighborhood.Proposition810b.Basic
import DomainTheory.Neighborhood.Proposition810b.isFinitary_of_projectionPair


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Exercise326

universe u v


variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}




variable {a b : ApproximableMap U U}












section ArrowCase

variable (a b : ApproximableMap U U)





/-- **Proposition 8.10(b), `→`-case.** `a, b` finitary projections `⟹` `a → b` is finitary, with
witnessing domain `D_a → D_b`. -/
theorem finitary_arrowComb (ha : IsFinitaryProjection a) (hb : IsFinitaryProjection b) :
    IsFinitary (arrowComb a b) :=
  isFinitary_of_projectionPair (IArrowComb a b) (JArrowComb a b) (JArrowComb_comp_IArrowComb a b)
    (IArrowComb_comp_JArrowComb a b ha hb).symm

end ArrowCase
end DomainTheory.Neighborhood
