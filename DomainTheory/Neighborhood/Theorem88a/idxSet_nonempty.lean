/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem88
import DomainTheory.Neighborhood.Definition610
import DomainTheory.Neighborhood.Lemma615
import Mathlib.Basic.Countable.Defs
import DomainTheory.Neighborhood.Theorem88a.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem

variable {α : Type*}

section Reencode

variable (e : ℕ → Set α)




theorem idxSet_nonempty (n : ℕ) : (idxSet e n).Nonempty := ⟨n, self_mem_idxSet e n⟩

end Reencode
end DomainTheory.Neighborhood
