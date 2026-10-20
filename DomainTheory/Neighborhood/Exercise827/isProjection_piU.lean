/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise826
import DomainTheory.Neighborhood.Exercise821
import DomainTheory.Neighborhood.Exercise827.Basic
import DomainTheory.Neighborhood.Exercise827.isProjection_piD


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap
































/-- **`Π(d)`, regarded as living in `𝒰` (`piU d`), is a projection, for every `d`.** Half of "for
`d` a polymorphic type, `Π(d)` is a type" (Definition 8.3's `IsProjection` clause) — Scott's own
"it is easy to check" — obtained "for free" from `isProjection_piD` via the same conjugation
gadget (`isProjection_conjArrow`) used for `subU` in Step 1. Note this does not even need `d` to
be a polymorphic type. -/
theorem isProjection_piU (d : ApproximableMap U U) : IsProjection (piU d) :=
  isProjection_conjArrow (isProjection_piD d)

end DomainTheory.Neighborhood
