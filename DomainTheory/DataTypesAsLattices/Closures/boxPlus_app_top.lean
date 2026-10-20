/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.squareFst_top
import DomainTheory.DataTypesAsLattices.Closures.squareSnd_top
import DomainTheory.DataTypesAsLattices.Closures.topElem_ne_botElem
import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app_mixed


namespace DomainTheory.DataTypesAsLattices































theorem boxPlus_app_top (a b : Pomega) :
    funOf (boxPlus a b) topElem = topElem :=
  boxPlus_app_mixed (by rw [squareFst_top]; exact topElem_ne_botElem)
    (by rw [squareSnd_top]; exact topElem_ne_botElem)

end DomainTheory.DataTypesAsLattices
