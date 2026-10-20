/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic


namespace DomainTheory.DataTypesAsLattices




























/-- **Scott 1976, (2.7).** Conditional cases. -/
theorem eq_2_7_bot (x y : Pomega) : condSet botElem x y = botElem := by
  ext n
  simp [condSet, botElem]

end DomainTheory.DataTypesAsLattices
