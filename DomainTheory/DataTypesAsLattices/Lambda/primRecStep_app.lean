/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.primRecStep_body_isScottContinuous_n


namespace DomainTheory.DataTypesAsLattices















































theorem primRecStep_app (a f u n : Pomega) :
    funOf (primRecStep a f u) n =
      condSet n a (funOf (funOf f (predSet n)) (funOf u (predSet n))) :=
  beta (primRecStep_body_isScottContinuous_n a f u) n

end DomainTheory.DataTypesAsLattices
