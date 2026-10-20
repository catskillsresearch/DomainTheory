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
import DomainTheory.DataTypesAsLattices.Enumeration.valStep_app


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices



























theorem valStep_app_zero (v : Pomega) :
    funOf (valStep v) (ofNat 0) = Gcomb := by
  rw [valStep_app]
  exact eq_2_7_zero Gcomb (minExtend (valStepValue v) (ofNat 0))

end DomainTheory.DataTypesAsLattices
