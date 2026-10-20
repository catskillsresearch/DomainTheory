/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic


namespace DomainTheory.DataTypesAsLattices















































theorem succSet_ofNat (j : ℕ) : succSet (ofNat j) = ofNat (j + 1) := by
  ext k
  simp [succSet, ofNat]

end DomainTheory.DataTypesAsLattices
