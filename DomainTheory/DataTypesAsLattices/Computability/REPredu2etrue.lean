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




theorem REPred.true {α} [Primcodable α] : REPred fun _ : α => True := by
  unfold REPred
  refine (Decidable.Partrec.const' (Part.some ())).of_eq fun _ => ?_
  ext
  simp [Part.assert]

end DomainTheory.DataTypesAsLattices
