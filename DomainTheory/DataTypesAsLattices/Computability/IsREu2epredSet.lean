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




theorem IsRE.predSet {x : Pomega} (hx : IsRE x) : IsRE (predSet x) :=
  REPred.of_eq (hx.comp Primrec.succ.to_comp) fun _ => Iff.rfl

end DomainTheory.DataTypesAsLattices
