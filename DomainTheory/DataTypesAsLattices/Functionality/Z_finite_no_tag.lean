/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.Z_finite_bound

@[expose] public section


namespace DomainTheory.DataTypesAsLattices



























theorem Z_finite_no_tag (p q m k : ℕ) :
    pair (max p q + 1) k ∉ Z m (e p) (e q) := by
  intro hk
  have hle := Z_finite_bound p q m _ hk
  exact (Nat.not_succ_le_self (max p q))
    ((pair_le_left (max p q + 1) k).trans hle)

end DomainTheory.DataTypesAsLattices
