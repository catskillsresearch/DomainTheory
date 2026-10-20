/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise812
public import DomainTheory.Neighborhood.Exercise812g4
public import DomainTheory.Neighborhood.Exercise813a.Basic
public import DomainTheory.Neighborhood.Exercise813a.levelSet_compl

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem









theorem V_compl_mem {X : Set ℕ} (hX : V.mem X) : Xᶜ = ∅ ∨ V.mem Xᶜ := by
  obtain ⟨k, m, rfl, -⟩ := hX
  rw [levelSet_compl]
  rcases (levelSet _ _).eq_empty_or_nonempty with h | h
  · exact Or.inl h
  · exact Or.inr ⟨k, _, rfl, h⟩

end DomainTheory.Neighborhood
