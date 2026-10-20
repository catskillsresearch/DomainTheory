/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Continuous
import DomainTheory.DataTypesAsLattices.Graph.Basic
import DomainTheory.DataTypesAsLattices.Graph.theorem_1_2_i


namespace DomainTheory.DataTypesAsLattices






/-- **Scott 1976, (β) for continuous `τ`.** `(λ x. τ)(y) = τ[y/x]`. -/
theorem beta {τ : Pomega → Pomega} (hτ : IsScottContinuous τ) (y : Pomega) :
    funOf (lam τ) y = τ y := by
  simp [lam, theorem_1_2_i hτ]

end DomainTheory.DataTypesAsLattices
