/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.boool_map_isScottContinuous


namespace DomainTheory.DataTypesAsLattices



































theorem boool_app (u : Pomega) :
    funOf boool u = condSet u (ofNat 0) (succSet topElem) :=
  beta boool_map_isScottContinuous u

end DomainTheory.DataTypesAsLattices
