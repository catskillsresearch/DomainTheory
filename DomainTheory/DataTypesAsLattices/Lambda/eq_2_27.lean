/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.eq_2_25
import DomainTheory.DataTypesAsLattices.Lambda.primRecVal_fix


namespace DomainTheory.DataTypesAsLattices















































/-- **Scott 1976, (2.27).** `p̂ = Y(λu λn∈ω. n ⊃ a, f(n−1)(u(n−1)))`. -/
theorem eq_2_27 (a f x : Pomega) :
    primRecHat a f x = funOf (funOf dollarC (fix (primRecStep a f))) x := by
  rw [eq_2_25]
  ext k
  constructor
  · intro hk
    obtain ⟨n, hn, hkn⟩ := Set.mem_iUnion₂.mp hk
    refine Set.mem_iUnion₂.mpr ⟨n, hn, ?_⟩
    simpa [primRecVal_fix] using hkn
  · intro hk
    obtain ⟨n, hn, hkn⟩ := Set.mem_iUnion₂.mp hk
    refine Set.mem_iUnion₂.mpr ⟨n, hn, ?_⟩
    simpa [primRecVal_fix] using hkn

end DomainTheory.DataTypesAsLattices
