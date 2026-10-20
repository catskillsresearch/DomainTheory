/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices






































/-- **Scott 1976, Theorem 4.3 (i).** On elements, `a ∘→ b` acts as `b ∘ − ∘ a`,
and that action is idempotent when `a, b` are retracts. -/
theorem theorem_4_3_i {a b u : Pomega} (ha : IsRetract a) (hb : IsRetract b) :
    funOf (arrowR a b) (funOf (arrowR a b) u) = funOf (arrowR a b) u := by
  rw [arrowR_app, arrowR_app]
  apply graph_ext
  intro x
  simp [comp_app, retract_app ha, retract_app hb]

end DomainTheory.DataTypesAsLattices
