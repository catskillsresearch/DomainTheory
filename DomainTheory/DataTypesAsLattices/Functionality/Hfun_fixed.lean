/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.HF_isScottContinuous


namespace DomainTheory.DataTypesAsLattices
















































theorem Hfun_fixed : HF Hfun = Hfun :=
  (theorem_1_4 HF_isScottContinuous).1

end DomainTheory.DataTypesAsLattices
