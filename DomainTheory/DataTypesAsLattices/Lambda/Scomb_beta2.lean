/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.Scomb_mid_cont
import DomainTheory.DataTypesAsLattices.Lambda.Scomb_beta


namespace DomainTheory.DataTypesAsLattices

































theorem Scomb_beta2 (f g : Pomega) :
    funOf (funOf Scomb f) g =
      graph (fun x => funOf (funOf f x) (funOf g x)) := by
  rw [Scomb_beta]
  exact beta (Scomb_mid_cont f) g

end DomainTheory.DataTypesAsLattices
