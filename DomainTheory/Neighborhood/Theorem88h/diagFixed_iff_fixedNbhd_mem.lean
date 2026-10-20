/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem85
import DomainTheory.Neighborhood.Definition72
import DomainTheory.Neighborhood.Theorem88h.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}


/-- `DiagFixed P a n` is exactly `(fixedNbhd a).mem (P.X n)`, since `P.X n` is always already a
`V`-neighbourhood (`P.mem_X`). -/
theorem diagFixed_iff_fixedNbhd_mem (P : ComputablePresentation V) (a : ApproximableMap V V)
    (n : ℕ) : DiagFixed P a n ↔ (fixedNbhd a).mem (P.X n) :=
  (and_iff_right (P.mem_X n)).symm

end DomainTheory.Neighborhood
