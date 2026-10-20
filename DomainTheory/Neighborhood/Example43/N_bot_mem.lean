/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Example23
import DomainTheory.Neighborhood.Theorem41
import DomainTheory.Neighborhood.Example43.Basic


namespace DomainTheory.Neighborhood.Example43

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap












/-- `⊥ ∈ N` reads: a neighbourhood lies in `⊥` iff it is the whole space `ℕ`. -/
theorem N_bot_mem {X : Set ℕ} : N.bot.mem X ↔ X = Set.univ := NeighborhoodSystem.mem_bot N

end DomainTheory.Neighborhood.Example43
