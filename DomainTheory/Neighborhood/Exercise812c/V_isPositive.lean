/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise812
public import DomainTheory.Neighborhood.IntervalPrimrec
public import DomainTheory.Neighborhood.Theorem88
public import DomainTheory.Neighborhood.Exercise812c.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem








/-- **`V` is Positive**: `levelSet_inter` presents *any* raw intersection unconditionally, so only
non-emptiness can obstruct `V.mem (X ∩ Y)`. -/
theorem V_isPositive : V.IsPositive := by
  rintro X Y ⟨k₁, m₁, rfl, -⟩ ⟨k₂, m₂, rfl, -⟩
  refine ⟨fun ⟨k, m, heq, hne⟩ => hne, fun hne => ⟨max k₁ k₂, _, levelSet_inter k₁ m₁ k₂ m₂, hne⟩⟩

end DomainTheory.Neighborhood
