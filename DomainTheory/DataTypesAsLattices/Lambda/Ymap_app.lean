/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.fix_param_isScottContinuous


namespace DomainTheory.DataTypesAsLattices

















































theorem Ymap_app {g : Pomega → Pomega → Pomega}
    (hgx : ∀ y, IsScottContinuous (fun x => g x y))
    (hgy : ∀ x, IsScottContinuous (fun y => g x y)) (x : Pomega) :
    funOf (Ymap g) x = fix (g x) :=
  beta (fix_param_isScottContinuous hgx hgy) x

end DomainTheory.DataTypesAsLattices
