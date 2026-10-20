/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.selfArrowStep_isScottContinuous


namespace DomainTheory.DataTypesAsLattices


































/-- **Scott 1976, (5.25).** `d = I ∪ (d ∘→ d)`. -/
theorem eq_5_25 : dEq = Icomb ∪ arrowR dEq dEq :=
  (theorem_1_4 selfArrowStep_isScottContinuous).1.symm

end DomainTheory.DataTypesAsLattices
