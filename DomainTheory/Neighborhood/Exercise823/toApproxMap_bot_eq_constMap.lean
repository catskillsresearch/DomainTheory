/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem86
import DomainTheory.Neighborhood.Theorem41
import DomainTheory.Neighborhood.Exercise315
import DomainTheory.Neighborhood.Exercise816
import DomainTheory.Neighborhood.Exercise823.Basic
import DomainTheory.Neighborhood.Exercise823.rel_master_of_mem


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Sub8_6

namespace Exercise823

variable {α : Type} {E : NeighborhoodSystem α}


/-- **`toApproxMap` of the function space's own bottom element is the constant-bottom map.**
Mirrors `Theorem616.lean`'s `botStrict_rel` for the (non-strict) function space `funSpace E E`. -/
theorem toApproxMap_bot_eq_constMap (E : NeighborhoodSystem α) :
    toApproxMap (funSpace E E).bot = constMap E E.bot := by
  apply ApproximableMap.ext
  intro X Y
  simp only [toApproxMap_rel, mem_bot, constMap_rel]
  constructor
  · intro h
    have hcb : constMap E E.bot ∈ step X Y := by rw [h]; trivial
    rwa [mem_step, constMap_rel, mem_bot] at hcb
  · rintro ⟨hX, rfl⟩
    exact Set.eq_univ_of_forall fun f => rel_master_of_mem f hX

end Exercise823
end DomainTheory.Neighborhood
