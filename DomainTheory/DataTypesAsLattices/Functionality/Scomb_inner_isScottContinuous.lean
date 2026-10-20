/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.continuous_tuple


namespace DomainTheory.DataTypesAsLattices






















theorem Scomb_inner_isScottContinuous (u v : Pomega) :
    IsScottContinuous (fun x => funOf (funOf u x) (funOf v x)) :=
  continuous_tuple
    (fun y => funOf_isScottContinuous_left y)
    (fun t => funOf_isScottContinuous t)
    (funOf_isScottContinuous u)
    (funOf_isScottContinuous v)

end DomainTheory.DataTypesAsLattices
