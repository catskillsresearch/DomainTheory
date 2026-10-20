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
public import DomainTheory.DataTypesAsLattices.Enumeration.secondRecVal_app
public import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_12

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

















































/-- **Scott 1976, Theorem 3.3 (iii)** from (i) and (ii):
`val(rec(n)) = val(n)(rec(n))`. -/
theorem theorem_3_3_from_v (v : ℕ → ℕ) (n : ℕ)
    (hv : valNat (v n) = secondRecVal (valNat n)) :
    valNat (recNat v n) = funOf (valNat n) (ofNat (recNat v n)) := by
  rw [recNat, valNat_apply, hv, eq_3_12, secondRecVal_app]
  ext k
  constructor
  · intro hk
    obtain ⟨m, hm, hkm⟩ := Set.mem_iUnion₂.mp hk
    simp [ofNat] at hm; subst hm; exact hkm
  · intro hk
    exact Set.mem_iUnion₂.mpr ⟨v n, rfl, hk⟩

end DomainTheory.DataTypesAsLattices
