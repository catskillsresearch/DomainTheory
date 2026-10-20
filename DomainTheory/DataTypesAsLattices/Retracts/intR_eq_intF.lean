/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.FixedLattices
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Retracts.Basic
import DomainTheory.DataTypesAsLattices.Retracts.intF_isScottContinuous


namespace DomainTheory.DataTypesAsLattices














































theorem intR_eq_intF : intF intR = intR :=
  (theorem_1_4 intF_isScottContinuous).1

end DomainTheory.DataTypesAsLattices
