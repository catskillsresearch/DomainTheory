/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic


namespace DomainTheory.DataTypesAsLattices















































theorem hApply_isScottContinuous_e (H t : Pomega) :
    IsScottContinuous (fun e => hApply H e t) :=
  theorem_1_3 (f := fun u => funOf u t) (g := funOf H)
    (funOf_isScottContinuous_left t) (funOf_isScottContinuous H)

end DomainTheory.DataTypesAsLattices
