/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
module

public import Mathlib.Order.CompleteLattice.Defs
import all Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Data.Finset.Basic
import all Mathlib.Data.Finset.Basic
public import DomainTheory.DataTypesAsLattices.FixedLattices.IsDirectedSet
public import DomainTheory.DataTypesAsLattices.FixedLattices.completeLatticeLE
public import DomainTheory.DataTypesAsLattices.FixedLattices.completeLatticeSupSet
public import DomainTheory.DataTypesAsLattices.FixedLattices.completeLatticePreorder

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- The way-below relation, phrased using directed suprema. -/
def WayBelow {α : Type u} [CompleteLattice α] (x y : α) : Prop :=
  ∀ s : Set α, @IsDirectedSet α completeLatticePreorder s →
    @LE.le α completeLatticeLE y (@sSup α completeLatticeSupSet s) →
    ∃ z ∈ s, @LE.le α completeLatticeLE x z

end DomainTheory.DataTypesAsLattices
