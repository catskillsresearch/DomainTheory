/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Proposition810
public import DomainTheory.Neighborhood.Theorem86
public import DomainTheory.Neighborhood.Proposition810b.Basic
public import DomainTheory.Neighborhood.Proposition810b.isFinitary_of_projectionPair

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Exercise326

universe u v


variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}




variable {a b : ApproximableMap U U}








section SumCase

variable (a b : ApproximableMap U U)






/-- **Proposition 8.10(b), `+`-case.** `a, b` finitary projections `⟹` `a + b` is finitary, with
witnessing domain `D_a + D_b`. -/
theorem finitary_sumComb (ha : IsFinitaryProjection a) (hb : IsFinitaryProjection b) :
    IsFinitary (sumComb a b) :=
  isFinitary_of_projectionPair (ISumComb a b) (JSumComb a b) (JSumComb_comp_ISumComb a b)
    (ISumComb_comp_JSumComb a b ha hb).symm

end SumCase
end DomainTheory.Neighborhood
