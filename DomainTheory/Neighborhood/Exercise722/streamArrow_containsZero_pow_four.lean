/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Basic
import DomainTheory.Neighborhood.Theorem41
import Mathlib.Data.Set.Insert
import DomainTheory.Neighborhood.Exercise722.Basic
import DomainTheory.Neighborhood.Exercise722.streamArrow_mul_self


namespace DomainTheory.Neighborhood

namespace Exercise722

open NeighborhoodSystem ApproximableMap




























/-- **Scott's fourth equation (the concrete numeric instance).** `01⃗·01⃗·01⃗·01⃗ = 01⃗·01⃗`, for
`01⃗ := streamArrow [false, true]`. Follows from `streamArrow_mul_self` applied twice. -/
theorem streamArrow_containsZero_pow_four :
    mulElem
        (mulElem (streamArrow [false, true]) (streamArrow [false, true]))
        (mulElem (streamArrow [false, true]) (streamArrow [false, true]))
      = mulElem (streamArrow [false, true]) (streamArrow [false, true]) := by
  rw [streamArrow_mul_self, streamArrow_mul_self]

end Exercise722
end DomainTheory.Neighborhood
