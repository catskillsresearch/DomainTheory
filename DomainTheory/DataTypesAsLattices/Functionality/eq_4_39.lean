/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.lambF_isScottContinuous


namespace DomainTheory.DataTypesAsLattices
































/-- **Scott 1976, (4.39).** `lamb = int ⊕ (lamb ∘→ lamb)`. -/
theorem eq_4_39 : lambR = plusR intR (arrowR lambR lambR) := by
  have hY : lambR = fix lambF := theorem_2_5 lambF_isScottContinuous
  have hfix : lambF lambR = lambR := by
    rw [hY]
    exact (theorem_1_4 lambF_isScottContinuous).1
  exact hfix.symm

end DomainTheory.DataTypesAsLattices
