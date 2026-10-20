/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst36
public import DomainTheory.DataTypesAsLattices.Retracts.RetractInverseLimit
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst55

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- A coherent inverse-limit sequence is increasing in the ambient
powerset order. -/
theorem inverseLimit_mono {F : Pomega → Pomega}
    (hf : IsScottContinuous F) (v : RetractInverseLimit F) :
    ∀ n, v.1 n ⊆ v.1 (n + 1) := by
  intro n
  rw [v.property.2 n]
  have hcode : iterateBot F n ⊆ iterateBot F (n + 1) :=
    iterateBot_mono hf n
  have h := funOf_monotone_left hcode (v.1 (n + 1))
  rw [← v.property.1 (n + 1)] at h
  exact h

end DomainTheory.DataTypesAsLattices
