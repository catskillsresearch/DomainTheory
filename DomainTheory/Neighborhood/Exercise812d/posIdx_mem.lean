/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise812c
import DomainTheory.Neighborhood.Definition71
import DomainTheory.Neighborhood.Definition72
import DomainTheory.Neighborhood.Exercise718
import DomainTheory.Neighborhood.Exercise812d.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718









namespace IsComputableSplit

variable {α γ : Type*} {V : NeighborhoodSystem α} {W : NeighborhoodSystem γ}
  {P : ComputablePresentation V} {Q : ComputablePresentation W}

/-- The split's first output is a genuine `W`-neighbourhood whenever it is non-empty (immediate
from `posIdx_spec` and `Q.mem_X`). Unlike the structure's original (unconditional) design, this is
now conditional on `(split …).1 ≠ ∅` — see `posIdx_spec`'s docstring. -/
theorem posIdx_mem (h : IsComputableSplit P Q split) (n m k : ℕ)
    (hne : (split (P.X n) (Q.X m) (P.X k)).1 ≠ ∅) :
    W.mem (split (P.X n) (Q.X m) (P.X k)).1 := by
  rw [h.posIdx_spec n m k hne]; exact Q.mem_X _

end IsComputableSplit
end DomainTheory.Neighborhood
