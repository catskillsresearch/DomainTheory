/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.funOf_e_union_fresh
import DomainTheory.DataTypesAsLattices.Functionality.normalized_finite_app


namespace DomainTheory.DataTypesAsLattices






























theorem normalized_finite_fresh_app (p q m : ℕ) :
    funOf (graph (fun y => funOf (e p) y))
        (Z m (e p) (e q) ∪ {pair (max p q + 1) m}) =
      Z (m + 1) (e p) (e q) := by
  rw [normalized_finite_app,
    funOf_e_union_fresh p (max p q + 1) m _
      (Nat.lt_succ_of_le (Nat.le_max_left p q))]
  rfl

end DomainTheory.DataTypesAsLattices
