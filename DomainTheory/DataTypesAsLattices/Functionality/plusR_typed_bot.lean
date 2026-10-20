/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.plusR_app


namespace DomainTheory.DataTypesAsLattices















theorem plusR_typed_bot (a b : Pomega) : typed botElem (plusR a b) := by
  rw [typed, plusR_app, funOf_bot, dcondSet_bot]

end DomainTheory.DataTypesAsLattices
