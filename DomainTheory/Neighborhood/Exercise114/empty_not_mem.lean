/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic
import DomainTheory.Neighborhood.Exercise114.Basic


namespace DomainTheory.Neighborhood.Exercise114

open DomainTheory.Neighborhood NeighborhoodSystem


theorem empty_not_mem : ¬ mem (∅ : Set ℕ) := by
  rintro (h | ⟨_, h⟩)
  · exact Set.empty_ne_univ h
  · exact Set.not_nonempty_empty h

end DomainTheory.Neighborhood.Exercise114
