/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise414
import DomainTheory.Neighborhood.Theorem46
import DomainTheory.Neighborhood.Exercise422.Basic


namespace DomainTheory.Neighborhood.Exercise422

open DomainTheory.Neighborhood DomainTheory.Neighborhood.Exercise414

variable {M : Type*} (zero : M) (succ : M → M)











/-- **Exercise 4.22 (Scott 1981, PRG-19).** *Yes:* whenever `N*` satisfies (i) and (ii), there is a
subset `N ⊆ N*` (carrying the inherited structure) satisfying (i), (ii), and (iii). -/
theorem exists_peano_submodel (hzero : ∀ n, zero ≠ succ n) (hinj : Function.Injective succ) :
    Nonempty (PeanoModel (Nat' zero succ)) :=
  ⟨peanoSub zero succ hzero hinj⟩

end DomainTheory.Neighborhood.Exercise422
