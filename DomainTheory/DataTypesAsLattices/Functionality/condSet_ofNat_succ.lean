/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic


namespace DomainTheory.DataTypesAsLattices



theorem condSet_ofNat_succ (n : ℕ) (x y : Pomega) :
    condSet (ofNat (n + 1)) x y = y := by
  ext k
  simp [condSet, ofNat]

end DomainTheory.DataTypesAsLattices
