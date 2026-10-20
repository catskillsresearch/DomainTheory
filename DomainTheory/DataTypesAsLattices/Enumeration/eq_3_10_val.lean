/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_8_val
public import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_9_val
public import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_10_apply

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


































theorem eq_3_10_val : valNat 12 = sucC := by
  have : valNat 12 = valNat (applyNat 3 1) := by simp [eq_3_10_apply]
  rw [this, valNat_apply, eq_3_9_val, eq_3_8_val]
  have : zeroC = ofNat 0 := rfl
  simpa [this] using Gpack_zero

end DomainTheory.DataTypesAsLattices
