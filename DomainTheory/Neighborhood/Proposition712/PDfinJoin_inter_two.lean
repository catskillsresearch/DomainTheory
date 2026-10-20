/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Definition711
public import DomainTheory.Neighborhood.Definition72
public import DomainTheory.Neighborhood.ApproximableExercises
public import DomainTheory.Neighborhood.Product
public import DomainTheory.Neighborhood.Proposition710
public import DomainTheory.Neighborhood.Theorem74
public import DomainTheory.Neighborhood.Lemma615
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.Neighborhood.Proposition712.Basic
public import DomainTheory.Neighborhood.Proposition712.PDfinJoin_pair

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)








/-- **Proposition 7.12 — binary intersection law (membership form).** `{x, y}` meets `W` iff both
singleton joins do. The general `n`-ary fold `{x₀,…,x_{n-1}} = ⋂ᵢ {xᵢ}` follows by iterating
`PDfinJoin_pair`. -/
theorem PDfinJoin_inter_two (x y : V.Element) {W : Set (Set α)} :
    (V.PDfinJoin 2 ![x, y]).mem W ↔
      (V.PDsingleton x).mem W ∧ (V.PDsingleton y).mem W := by
  rw [← PDsingletonMeet_mem, ← PDfinJoin_pair]

end NeighborhoodSystem
end DomainTheory.Neighborhood
