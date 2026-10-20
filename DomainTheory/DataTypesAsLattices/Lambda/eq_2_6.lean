/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic


namespace DomainTheory.DataTypesAsLattices























/-- **Scott 1976, (2.6).** `0 − 1 = ⊥`. -/
theorem eq_2_6 : predSet (ofNat 0) = botElem := by
  ext k
  simp [predSet, ofNat, botElem]

end DomainTheory.DataTypesAsLattices
