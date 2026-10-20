/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Computability.Halting
import DomainTheory.DataTypesAsLattices.Computability
import DomainTheory.DataTypesAsLattices.Functionality
import DomainTheory.DataTypesAsLattices.Enumeration.Basic
import DomainTheory.DataTypesAsLattices.Enumeration.secondRecVal_isScottContinuous


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices








































theorem secondRecVal_app (u x : Pomega) :
    funOf (secondRecVal u) x =
      ⋃ m ∈ x, funOf u (ofNat (applyNat m (num m))) :=
  beta (secondRecVal_isScottContinuous u) x

end DomainTheory.DataTypesAsLattices
