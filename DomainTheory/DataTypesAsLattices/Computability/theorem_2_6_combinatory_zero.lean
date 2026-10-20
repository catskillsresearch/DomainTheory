/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Computability.RE
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Computability.Basic


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




/-- Combinatory elements are generated from the six constants, matching
the LAMBDA-definable closed terms of Theorem 2.4. -/
theorem theorem_2_6_combinatory_zero : IsLambdaDefinable zeroC :=
  ⟨Term.zero, rfl⟩

end DomainTheory.DataTypesAsLattices
