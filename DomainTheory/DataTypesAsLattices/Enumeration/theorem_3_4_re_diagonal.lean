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
import DomainTheory.DataTypesAsLattices.Enumeration.theorem_3_4_diagonal


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices



















































/-- **Scott 1976, Theorem 3.4** for an r.e. undefined-index set. -/
theorem theorem_3_4_re_diagonal {val : ℕ → Pomega} {v : ℕ → ℕ}
    (hv : ∀ k, val (v k) = ofNat k ∩ val k)
    (_hRE : IsRE {j | val j = botElem})
    (hex : ∃ k, val k = {i | v i ∈ {j | val j = botElem}}) : False :=
  theorem_3_4_diagonal hv rfl hex

end DomainTheory.DataTypesAsLattices
