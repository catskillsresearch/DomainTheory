/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.union_left_isScottContinuous


namespace DomainTheory.DataTypesAsLattices































theorem union_const_left_isScottContinuous (c : Pomega) :
    IsScottContinuous (fun x => c ∪ x) := by
  have : (fun x : Pomega => c ∪ x) = (fun x => x ∪ c) := by
    funext x; exact Set.union_comm c x
  rw [this]
  exact union_left_isScottContinuous c

end DomainTheory.DataTypesAsLattices
