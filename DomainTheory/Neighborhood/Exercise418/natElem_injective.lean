/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Example43
import DomainTheory.Neighborhood.Exercise418.Basic


namespace DomainTheory.Neighborhood.Exercise418

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap Example43


/-- **Exercise 4.18 (Scott 1981, PRG-19).** The numerals are distinct: `n̂ = m̂ ⟹ n = m`. -/
theorem natElem_injective {n m : ℕ} (h : natElem n = natElem m) : n = m := by
  have hmem : (natElem m).mem {n} := h ▸ (mem_natElem_iff.mpr (Or.inr rfl))
  rw [mem_natElem_iff] at hmem
  rcases hmem with hu | hs
  · exact absurd hu (singleton_ne_univ n)
  · exact singleton_nat_inj hs

end DomainTheory.Neighborhood.Exercise418
