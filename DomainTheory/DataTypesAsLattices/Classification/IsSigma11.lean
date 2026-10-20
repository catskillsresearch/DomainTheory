/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
import all Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.IsBooleanOpen

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

def IsSigma11 (U : Set Pomega) : Prop :=
  ∃ f g, IsScottContinuous f ∧ IsScottContinuous g ∧
    U = {x | ∃ y, funOf (f x) y = funOf (g x) y}

end DomainTheory.DataTypesAsLattices
