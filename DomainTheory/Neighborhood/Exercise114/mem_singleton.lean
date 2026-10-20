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



theorem mem_singleton (n : ℕ) : mem {n} :=
  Or.inr ⟨Set.finite_singleton n, Set.singleton_nonempty n⟩

end DomainTheory.Neighborhood.Exercise114
