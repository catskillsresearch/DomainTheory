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
import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_12
import DomainTheory.DataTypesAsLattices.Enumeration.valNat_interCode


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices
























































theorem valNat_diagonalInterCode (n : ℕ) :
    valNat (diagonalInterCode n) = ofNat n ∩ valNat n := by
  rw [diagonalInterCode, valNat_apply, valNat_apply, valNat_interCode,
    eq_3_12, eq_2_17]

end DomainTheory.DataTypesAsLattices
