/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Fixpoints
public import DomainTheory.DataTypesAsLattices.Retracts.lfpAbove
public import DomainTheory.DataTypesAsLattices.Retracts.sUnion_Fixpoints_le_image
public import DomainTheory.DataTypesAsLattices.Retracts.lfpAbove_fixed

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

theorem lfpAbove_mem {f : Pomega → Pomega} (hf : IsScottContinuous f)
    {A : Set Pomega} (hA : A ⊆ Fixpoints f) :
    lfpAbove f (⋃₀ A) ∈ Fixpoints f :=
  lfpAbove_fixed hf (sUnion_Fixpoints_le_image hf hA)

end DomainTheory.DataTypesAsLattices
