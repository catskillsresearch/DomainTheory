/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.Kcomb_app2
import DomainTheory.DataTypesAsLattices.Functionality.Kcomb_isGraph
import DomainTheory.DataTypesAsLattices.Functionality.Kcomb_app_isGraph


namespace DomainTheory.DataTypesAsLattices






















/-- **Scott 1976, Theorem 7.3 (ii).** `K : A → (B → A)`. -/
theorem theorem_7_3_ii (A B : RestrictedEquiv) :
    (arrowE A (arrowE B A)).mem Kcomb := by
  refine ⟨Kcomb_isGraph, Kcomb_isGraph, ?_⟩
  intro x x' hx
  refine ⟨Kcomb_app_isGraph x, Kcomb_app_isGraph x', ?_⟩
  intro y y' _hy
  simpa [Kcomb_app2] using hx

end DomainTheory.DataTypesAsLattices
