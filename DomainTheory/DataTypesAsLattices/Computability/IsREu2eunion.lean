/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Computability.RE
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Computability.Basic
import DomainTheory.DataTypesAsLattices.Computability.REPredu2eor


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




theorem IsRE.union {u v : Pomega} (hu : IsRE u) (hv : IsRE v) : IsRE (u ∪ v) :=
  REPred.of_eq (REPred.or hu hv) fun _ => Iff.rfl

end DomainTheory.DataTypesAsLattices
