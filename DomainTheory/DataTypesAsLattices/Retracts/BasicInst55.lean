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

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

instance (F : Pomega → Pomega) : PartialOrder (RetractInverseLimit F) where
  le v w := ∀ n, v.1 n ⊆ w.1 n
  le_refl _ _ := subset_rfl
  le_trans _ _ _ hvw hwz n := subset_trans (hvw n) (hwz n)
  le_antisymm v w hvw hwv := by
    apply Subtype.ext
    funext n
    exact Set.Subset.antisymm (hvw n) (hwv n)

end DomainTheory.DataTypesAsLattices
