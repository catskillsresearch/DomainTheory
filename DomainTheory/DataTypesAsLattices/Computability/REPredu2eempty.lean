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




theorem REPred.empty : REPred fun _ : ℕ => False := by
  unfold REPred
  refine (Partrec.none (α := ℕ) (σ := Unit)).of_eq fun _ => ?_
  ext
  simp [Part.assert]

end DomainTheory.DataTypesAsLattices
