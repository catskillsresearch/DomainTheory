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

















theorem evalC_isScottContinuous :
    IsScottContinuous (fun u => funOf (funOf u (ofNat 0)) (funOf u (ofNat 1))) :=
  continuous_tuple
    (fun y => funOf_isScottContinuous_left y)
    (fun t => funOf_isScottContinuous t)
    (funOf_isScottContinuous_left (ofNat 0))
    (funOf_isScottContinuous_left (ofNat 1))

end DomainTheory.DataTypesAsLattices
