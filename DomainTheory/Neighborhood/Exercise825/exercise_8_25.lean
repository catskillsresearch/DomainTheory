/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise825Unit
import DomainTheory.Neighborhood.Exercise825FixedPoint
import DomainTheory.Neighborhood.Exercise825.Basic


namespace DomainTheory.Neighborhood

/-- **Exercise 8.25 (Scott 1981, PRG-19), the answer.** The concrete domain
`D := fixedNbhd (fixOp (tOpMap cCombinator))` (built in `Exercise825FixedPoint.lean` by the
fixed-point method of Exercise 8.23, applied to `T(a) := a → 𝒰^∞`) satisfies `D ≅ D → D`. -/
theorem exercise_8_25 :
    fixedNbhd (Exercise823.fixOp (tOpMap cCombinator)) ≅ᴰ
      funSpace (fixedNbhd (Exercise823.fixOp (tOpMap cCombinator)))
        (fixedNbhd (Exercise823.fixOp (tOpMap cCombinator))) :=
  exercise_8_25_main

end DomainTheory.Neighborhood
