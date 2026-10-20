/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.IsREu2eofFinset

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




/-- Finite `e j` is r.e. Named `of_e` so it does not shadow `e`. -/
theorem IsRE.of_e (j : ℕ) : IsRE (e j) := by
  let s := (Finset.range (j + 1)).filter (fun k => j.testBit k)
  have hs : (s : Set ℕ) = e j := by
    ext n
    constructor
    · intro hn
      simp [s] at hn
      exact mem_e.mpr hn.2
    · intro hn
      simp [s, Finset.mem_range, mem_e.mp hn,
        Nat.lt_succ_of_le (mem_e_le hn)]
  simpa [hs] using IsRE.ofFinset s

end DomainTheory.DataTypesAsLattices
