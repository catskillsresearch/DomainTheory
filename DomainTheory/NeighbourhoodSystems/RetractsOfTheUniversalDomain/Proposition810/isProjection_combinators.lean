/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Definition89
public import DomainTheory.Neighborhood.Definition83
public import DomainTheory.Neighborhood.Theorem69
public import DomainTheory.Neighborhood.Proposition810.Basic
public import DomainTheory.Neighborhood.Proposition810.isProjection_prodComb
public import DomainTheory.Neighborhood.Proposition810.isProjection_arrowComb
public import DomainTheory.Neighborhood.Proposition810.isProjection_sumComb

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Exercise326


variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}





/-- **Proposition 8.10 (Scott 1981, PRG-19), first half.** If `a, b : 𝒰 → 𝒰` are projections,
then so are `a+b`, `a×b`, and `a→b`. -/
theorem isProjection_combinators {a b : ApproximableMap U U}
    (ha : IsProjection a) (hb : IsProjection b) :
    IsProjection (sumComb a b) ∧ IsProjection (prodComb a b) ∧ IsProjection (arrowComb a b) :=
  ⟨isProjection_sumComb ha hb, isProjection_prodComb ha hb, isProjection_arrowComb ha hb⟩

end DomainTheory.Neighborhood
