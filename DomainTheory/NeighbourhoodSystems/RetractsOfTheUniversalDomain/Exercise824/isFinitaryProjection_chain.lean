/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise823
public import DomainTheory.Neighborhood.Exercise824.Basic
public import DomainTheory.Neighborhood.Exercise824.aOp_succ
public import DomainTheory.Neighborhood.Exercise824.bOp_succ
public import DomainTheory.Neighborhood.Exercise824.aOp_zero
public import DomainTheory.Neighborhood.Exercise824.bOp_zero

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Sub8_6 Exercise823

namespace Exercise824

variable {α : Type} {E : NeighborhoodSystem α}












/-- Every approximant pair `(aOp s t n, bOp s t n)` consists of finitary projections, provided
`s`/`t` send pairs of finitary projections to finitary projections. -/
theorem isFinitaryProjection_chain (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E))
    (hst : ∀ a b, IsFinitaryProjection a → IsFinitaryProjection b →
      IsFinitaryProjection (binOp s a b) ∧ IsFinitaryProjection (binOp t a b)) :
    ∀ n, IsFinitaryProjection (aOp s t n) ∧ IsFinitaryProjection (bOp s t n) := by
  intro n
  induction n with
  | zero =>
    rw [aOp_zero, bOp_zero]
    exact ⟨Exercise823.isFinitaryProjection_constMap_bot E,
      Exercise823.isFinitaryProjection_constMap_bot E⟩
  | succ k ih =>
    rw [aOp_succ, bOp_succ]
    exact hst _ _ ih.1 ih.2

end Exercise824
end DomainTheory.Neighborhood
