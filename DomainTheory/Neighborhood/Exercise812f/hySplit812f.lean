/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise812e
import DomainTheory.Neighborhood.UBisection2
import DomainTheory.Neighborhood.VDiff
import DomainTheory.Neighborhood.Exercise812f.Basic


namespace DomainTheory.Neighborhood

open Domain.Recursive NeighborhoodSystem



/-- **`8.12(g)(3)`, `V`-as-prober half**: `splitX812f` also satisfies `SplitSpec'`, the mirror
image of `Exercise812eD.lean`'s `hxSplit812e`. The extra hypothesis it needs, `∀ j, UX j ≠ ∅`, is
immediate from `U_mem_UX`/`U.mem`'s own `X.Nonempty` conjunct (`Definition87.lean` line 96). -/
theorem hySplit812f : SplitSpec' U splitX812f :=
  ComputableBisection.splitFromBisection_isSplitSpec' VComputablePresentation V_isComputableDiff
    UBisection2 U_noMinimal V_isPositive V_noMinimal V_diffClosed
    (fun j => (U_mem_UX j).2.1.ne_empty)

end DomainTheory.Neighborhood
