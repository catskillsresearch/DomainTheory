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





















theorem outrightC_isScottContinuous :
    IsScottContinuous (fun u =>
      condSet (funOf u (ofNat 0)) botElem (funOf u (ofNat 1))) :=
  continuous_tuple
    (fun y => condSet_isScottContinuous_left botElem y)
    (fun tes => condSet_isScottContinuous_right tes botElem)
    (funOf_isScottContinuous_left (ofNat 0))
    (funOf_isScottContinuous_left (ofNat 1))

end DomainTheory.DataTypesAsLattices
