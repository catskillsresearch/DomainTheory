/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Definition87
public import DomainTheory.Neighborhood.Theorem85
public import Mathlib.Data.Nat.BitIndices
import all Mathlib.Data.Nat.BitIndices
public import Mathlib.Data.Nat.Bitwise
import all Mathlib.Data.Nat.Bitwise
public import Mathlib.Combinatorics.Colex
import all Mathlib.Combinatorics.Colex
public import DomainTheory.Neighborhood.Exercise812.Basic
public import DomainTheory.Neighborhood.Exercise812.levelSet_union_same_level

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem

















/-- **`V` is closed under binary union**, as long as the result is non-empty — mirrors
`Definition87.lean`'s `U_union_mem`, needed to reassemble Scott's literal finite unions. -/
theorem V_union_mem {X Y : Set ℕ} (hX : X = ∅ ∨ V.mem X) (hY : Y = ∅ ∨ V.mem Y) :
    X ∪ Y = ∅ ∨ V.mem (X ∪ Y) := by
  rcases hX with rfl | hX
  · simpa using hY
  rcases hY with rfl | hY
  · simpa using Or.inr hX
  obtain ⟨k₁, m₁, rfl, hXne⟩ := hX
  obtain ⟨k₂, m₂, rfl, -⟩ := hY
  have heq : levelSet k₁ m₁ ∪ levelSet k₂ m₂
      = levelSet (max k₁ k₂) (upsample k₁ (max k₁ k₂) m₁ ||| upsample k₂ (max k₁ k₂) m₂) := by
    rw [← levelSet_union_same_level, levelSet_upsample (le_max_left k₁ k₂),
      levelSet_upsample (le_max_right k₁ k₂)]
  exact Or.inr ⟨max k₁ k₂, _, heq, hXne.mono Set.subset_union_left⟩

end DomainTheory.Neighborhood
