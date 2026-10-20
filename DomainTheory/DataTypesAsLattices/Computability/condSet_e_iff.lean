/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Computability.RE
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Computability.Basic
import DomainTheory.DataTypesAsLattices.Computability.pos_bit_iff


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem condSet_e_iff (n0 n1 n2 m : ℕ) :
    m ∈ condSet (e n2) (e n0) (e n1) ↔
      (n0.testBit m = true ∧ n2.testBit 0 = true) ∨
        (n1.testBit m = true ∧ 2 ≤ n2) := by
  constructor
  · intro h
    rcases h with ⟨hm, h0⟩ | ⟨hm, ⟨k, hk⟩⟩
    · exact Or.inl ⟨mem_e.mp hm, mem_e.mp h0⟩
    · exact Or.inr ⟨mem_e.mp hm, (pos_bit_iff n2).1 ⟨k, mem_e.mp hk⟩⟩
  · intro h
    rcases h with ⟨hm, h0⟩ | ⟨hm, hn2⟩
    · exact Or.inl ⟨mem_e.mpr hm, mem_e.mpr h0⟩
    · obtain ⟨k, hk⟩ := (pos_bit_iff n2).2 hn2
      exact Or.inr ⟨mem_e.mpr hm, k, mem_e.mpr hk⟩

end DomainTheory.DataTypesAsLattices
