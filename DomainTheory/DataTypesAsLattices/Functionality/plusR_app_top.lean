/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.funOf_top
import DomainTheory.DataTypesAsLattices.Functionality.plusR_app


namespace DomainTheory.DataTypesAsLattices















theorem plusR_app_top (a b : Pomega) :
    funOf (plusR a b) topElem = topElem := by
  rw [plusR_app, funOf_top, dcondSet_top]

end DomainTheory.DataTypesAsLattices
