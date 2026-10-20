/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Basic
import Mathlib.Tactic
import DomainTheory.Neighborhood.Example14.Basic


namespace DomainTheory.Neighborhood.Example14













































namespace neighborhoodSystem

open NeighborhoodSystem
















theorem elemZero_lt_elem00 : elemZero < elem00 := by
  constructor
  · intro X hx
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · intro h
    rcases h leaf00 (Or.inr (Or.inr rfl)) with h1 | h1
    · exact leaf00_ne_master h1
    · exact leaf00_ne_left h1

end neighborhoodSystem
end DomainTheory.Neighborhood.Example14
