/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.Icomb_isGraph


namespace DomainTheory.DataTypesAsLattices






















/-- **Scott 1976, Theorem 7.3 (i).** `I : A → A`. -/
theorem theorem_7_3_i (A : RestrictedEquiv) :
    (arrowE A A).mem Icomb :=
  ⟨Icomb_isGraph, Icomb_isGraph, fun x y hxy => by simpa [Icomb_app] using hxy⟩

end DomainTheory.DataTypesAsLattices
