/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.Neighborhood.Exercise115.Basic

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise115

open DomainTheory.Neighborhood NeighborhoodSystem








theorem flat_empty_not_mem : ¬ flat.mem (∅ : Set ℕ) := by
  rintro (h | ⟨n, h⟩)
  · exact Set.empty_ne_univ h
  · exact absurd h.symm (Set.singleton_ne_empty n)

end DomainTheory.Neighborhood.Exercise115
