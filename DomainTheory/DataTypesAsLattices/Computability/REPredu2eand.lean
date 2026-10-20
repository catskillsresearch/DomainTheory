/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Computability.RE
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Computability.Basic
import DomainTheory.DataTypesAsLattices.Computability.REPredu2ecomp


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




theorem REPred.and {α} [Primcodable α] {p q : α → Prop}
    (hp : REPred p) (hq : REPred q) :
    REPred fun a => p a ∧ q a := by
  refine (hp.bind (hq.comp Computable.fst).to₂).of_eq fun a => ?_
  ext
  simp [Part.assert]

end DomainTheory.DataTypesAsLattices
