/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic


namespace DomainTheory.DataTypesAsLattices




























theorem eq_2_7_succ (x y : Pomega) (k : ℕ) :
    condSet (ofNat (k + 1)) x y = y := by
  ext n
  simp [condSet, ofNat]

end DomainTheory.DataTypesAsLattices
