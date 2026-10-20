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























































namespace IsComputableUnion

variable {α : Type*} {V : NeighborhoodSystem α} {P : ComputablePresentation V}

/-- **Under `UnionClosed`, the existential is unconditionally true** — every `X n ∪ X m` is a
genuine neighbourhood, hence indexed by `P.surj`. Mirrors
`IsComputableDiff.diff_exists_iff_ne_empty`, but simpler: `∪` has no "-or-empty" branch to rule
out, so this is a plain existence fact rather than an `iff`. Not needed to *state*
`IsComputableUnion` (kept off the structure itself, matching how `DiffClosed`/`UnionClosed` are
separate hypotheses from `ComputablePresentation` elsewhere in this file); recorded here for
convenience, though the eventual `(d)(4)(c)`/`(d)` instantiation is expected to discharge
`unionIdx_spec`'s hypothesis directly from `XPseq_mem`/`YPseq_mem`-style facts specific to the
atoms actually in play, rather than from a blanket `UnionClosed` on all of `D`. -/
theorem union_exists (hunion : V.UnionClosed) (n m : ℕ) :
    ∃ k, P.X k = P.X n ∪ P.X m :=
  P.surj (hunion (P.mem_X n) (P.mem_X m))

end IsComputableUnion
end DomainTheory.Neighborhood
