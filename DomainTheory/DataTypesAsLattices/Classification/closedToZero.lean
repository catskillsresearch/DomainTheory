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
public import DomainTheory.DataTypesAsLattices.Classification.charTop

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

/-- Three-valued characteristic of a Scott-closed set: `0` on `C`, `⊤` off `C`. -/
def closedToZero (C : Set Pomega) (x : Pomega) : Pomega :=
  ofNat 0 ∪ charTop Cᶜ x

end DomainTheory.DataTypesAsLattices
