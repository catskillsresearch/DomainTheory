/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.Scomb_inner_cont
import DomainTheory.DataTypesAsLattices.Lambda.Scomb_beta2


namespace DomainTheory.DataTypesAsLattices

































theorem Scomb_beta3 (f g x : Pomega) :
    funOf (funOf (funOf Scomb f) g) x = funOf (funOf f x) (funOf g x) := by
  rw [Scomb_beta2]
  exact beta (Scomb_inner_cont f g) x

end DomainTheory.DataTypesAsLattices
