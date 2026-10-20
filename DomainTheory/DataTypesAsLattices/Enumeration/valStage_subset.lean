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
public import DomainTheory.DataTypesAsLattices.Enumeration.valStep_app_zero
public import DomainTheory.DataTypesAsLattices.Enumeration.valStep_app_succ

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices



































theorem valStage_subset : ∀ s n,
    funOf (iterateBot valStep s) (ofNat n) ⊆ valNat n
  | 0, n => by simp [iterateBot, funOf, botElem]
  | s + 1, 0 => by
      rw [iterateBot, valStep_app_zero, valNat_zero]
  | s + 1, p + 1 => by
      rw [iterateBot, valStep_app_succ, valNat_succ]
      exact subset_trans
        (funOf_monotone_left
          (valStage_subset s (unpair p).1)
          (funOf (iterateBot valStep s) (ofNat (unpair p).2)))
        (funOf_monotone_right (valNat (unpair p).1)
          (valStage_subset s (unpair p).2))

end DomainTheory.DataTypesAsLattices
