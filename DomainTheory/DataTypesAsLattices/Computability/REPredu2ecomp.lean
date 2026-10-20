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




theorem REPred.comp {α β} [Primcodable α] [Primcodable β] {p : β → Prop}
    (hp : REPred p) {f : α → β} (hf : Computable f) :
    REPred fun a => p (f a) :=
  Partrec.comp hp hf

end DomainTheory.DataTypesAsLattices
