/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.Z_rel
import DomainTheory.DataTypesAsLattices.Functionality.Zcomb_app2
import DomainTheory.DataTypesAsLattices.Functionality.Zcomb_isGraph
import DomainTheory.DataTypesAsLattices.Functionality.Zcomb_app_isGraph


namespace DomainTheory.DataTypesAsLattices
























/-- **Scott 1976, Theorem 7.4 (i).** `Zₙ : (A → A) → (A → A)`. -/
theorem theorem_7_4_i (A : RestrictedEquiv) (n : ℕ) :
    (arrowE (arrowE A A) (arrowE A A)).mem (Zcomb n) := by
  refine ⟨Zcomb_isGraph n, Zcomb_isGraph n, ?_⟩
  intro f f' hf
  refine ⟨Zcomb_app_isGraph n f, Zcomb_app_isGraph n f', ?_⟩
  intro x y hxy
  simpa [Zcomb_app2] using Z_rel A n hf.2.2 hxy

end DomainTheory.DataTypesAsLattices
