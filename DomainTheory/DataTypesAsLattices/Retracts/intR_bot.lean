/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.FixedLattices
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Retracts.Basic
import DomainTheory.DataTypesAsLattices.Retracts.intR_app


namespace DomainTheory.DataTypesAsLattices














































theorem intR_bot : funOf intR botElem = botElem := by
  rw [intR_app, dcondSet_bot]

end DomainTheory.DataTypesAsLattices
