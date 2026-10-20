/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.curryC_isScottContinuous


namespace DomainTheory.DataTypesAsLattices

















theorem curryC_app (u : Pomega) :
    funOf curryC u = graph (fun x => graph (fun y => funOf u (pairSeq x y))) :=
  beta curryC_isScottContinuous u

end DomainTheory.DataTypesAsLattices
