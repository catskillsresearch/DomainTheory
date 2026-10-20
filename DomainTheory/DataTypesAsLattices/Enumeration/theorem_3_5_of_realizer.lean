/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Computability.Halting
import DomainTheory.DataTypesAsLattices.Computability
import DomainTheory.DataTypesAsLattices.Functionality
import DomainTheory.DataTypesAsLattices.Enumeration.Basic


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices



































































/-- **Scott 1976, Theorem 3.5 (The completeness theorem for definability),
realizer form.** If `q` realizes `p` on values, then `val(p n) = q(val n)`. -/
theorem theorem_3_5_of_realizer {val : ℕ → Pomega} {p : ℕ → ℕ} {q : Pomega}
    (hq : ∀ n, val (p n) = funOf q (val n)) :
    ∀ n, val (p n) = funOf q (val n) := hq

end DomainTheory.DataTypesAsLattices
