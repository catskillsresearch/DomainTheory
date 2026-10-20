/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.lambR_isRetract
import DomainTheory.DataTypesAsLattices.Functionality.expR_isRetract
import DomainTheory.DataTypesAsLattices.Functionality.envR_isRetract
import DomainTheory.DataTypesAsLattices.Functionality.typed_apply_retract


namespace DomainTheory.DataTypesAsLattices

















































theorem Hcomb_typed :
    typed Hcomb (arrowR expR (arrowR envR lambR)) :=
  typed_apply_retract
    (arrowR_isRetract expR_isRetract
      (arrowR_isRetract envR_isRetract lambR_isRetract))

end DomainTheory.DataTypesAsLattices
