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
import DomainTheory.DataTypesAsLattices.Enumeration.unionBits_eq


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


























































theorem e_eq_unionBits (j : ℕ) : e j = unionBits (bitList j) := by
  ext n
  constructor
  · intro hn
    have hnle : n ≤ j := mem_e_le hn
    have hbit : j.testBit n := by simpa [e] using hn
    have : n ∈ bitList j := by
      simp [bitList, List.mem_filter, List.mem_range, Nat.lt_succ_of_le hnle, hbit]
    simpa [unionBits_eq] using this
  · intro hn
    have : n ∈ bitList j := by simpa [unionBits_eq] using hn
    simp [bitList, List.mem_filter] at this
    simpa [e] using this.2

end DomainTheory.DataTypesAsLattices
