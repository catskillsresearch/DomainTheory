/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.squareFst_bot
import DomainTheory.DataTypesAsLattices.Closures.squareSnd_bot
import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app_empty


namespace DomainTheory.DataTypesAsLattices































theorem boxPlus_app_bot (a b : Pomega) :
    funOf (boxPlus a b) botElem = botElem :=
  boxPlus_app_empty squareFst_bot squareSnd_bot

end DomainTheory.DataTypesAsLattices
