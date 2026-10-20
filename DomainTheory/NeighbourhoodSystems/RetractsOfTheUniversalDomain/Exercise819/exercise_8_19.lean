/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise817
public import DomainTheory.Neighborhood.Proposition810b
public import DomainTheory.Neighborhood.Exercise326Sum
public import DomainTheory.Neighborhood.Exercise315
public import DomainTheory.Neighborhood.Exercise819.Basic
public import DomainTheory.Neighborhood.Exercise819.prod_trianglelefteq_of
public import DomainTheory.Neighborhood.Exercise819.sum_trianglelefteq_of

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Exercise326

universe u










/-- **Exercise 8.19.** If `T ⊴ E` and `E → E ⊴ E`, then `E + E ⊴ E` and `E × E ⊴ E`. -/
theorem exercise_8_19 {α : Type u} {E : NeighborhoodSystem α}
    (hE : ∀ X, E.mem X → X.Nonempty) (hT : TD ⊴ E) (hArrow : funSpace E E ⊴ E) :
    sum E E hE hE ⊴ E ∧ prod E E ⊴ E :=
  ⟨sum_trianglelefteq_of hE hT hArrow, prod_trianglelefteq_of hT hArrow⟩

end DomainTheory.Neighborhood
