/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Proposition810
import DomainTheory.Neighborhood.Theorem86
import DomainTheory.Neighborhood.Proposition810b.Basic
import DomainTheory.Neighborhood.Proposition810b.finitaryProjection_prodComb
import DomainTheory.Neighborhood.Proposition810b.finitaryProjection_sumComb
import DomainTheory.Neighborhood.Proposition810b.finitaryProjection_arrowComb


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Exercise326

universe u v


variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}




variable {a b : ApproximableMap U U}














/-- **Proposition 8.10(b) (Scott 1981, PRG-19), in full.** If `a, b : 𝒰 → 𝒰` are finitary
projections, then so are `a+b`, `a×b`, `a→b`, with `D_{a+b} ≅ D_a+D_b`, `D_{a×b} ≅ D_a×D_b`,
`D_{a→b} ≅ (D_a→D_b)`. -/
theorem finitaryProjection_combinators {a b : ApproximableMap U U}
    (ha : IsFinitaryProjection a) (hb : IsFinitaryProjection b) :
    IsFinitaryProjection (sumComb a b) ∧ IsFinitaryProjection (prodComb a b) ∧
      IsFinitaryProjection (arrowComb a b) :=
  ⟨finitaryProjection_sumComb a b ha hb, finitaryProjection_prodComb a b ha hb,
    finitaryProjection_arrowComb a b ha hb⟩

end DomainTheory.Neighborhood
