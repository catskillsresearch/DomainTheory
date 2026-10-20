/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.FixedLattices
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Retracts.Basic


namespace DomainTheory.DataTypesAsLattices


































































/-- `bool` is idempotent: mixed tags collapse to `⊤`, a fixed point of `⊒`. -/
theorem dcondSet_bool_idem (u : Pomega) :
    dcondSet (dcondSet u (ofNat 0) (ofNat 1)) (ofNat 0) (ofNat 1) =
      dcondSet u (ofNat 0) (ofNat 1) := by
  rcases dcondSet_cases u with h | h | h | h
  · rw [dcondSet_of_zero_not_pos h.1 h.2, dcondSet_ofNat_zero]
  · rw [dcondSet_of_pos_not_zero h.1 h.2, dcondSet_ofNat_one]
  · rw [dcondSet_of_mixed h.1 h.2, dcondSet_top]
  · rw [dcondSet_of_empty h.1 h.2, dcondSet_bot]

end DomainTheory.DataTypesAsLattices
