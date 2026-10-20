/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise414
public import DomainTheory.Neighborhood.Theorem46
public import DomainTheory.Neighborhood.Exercise422.Basic

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise422

open DomainTheory.Neighborhood DomainTheory.Neighborhood.Exercise414

variable {M : Type*} (zero : M) (succ : M → M)


theorem genOp_monotone : Monotone (genOp zero succ) := by
  intro x y hxy z hz
  rcases hz with hz | ⟨a, ha, rfl⟩
  · exact Or.inl hz
  · exact Or.inr ⟨a, hxy ha, rfl⟩

end DomainTheory.Neighborhood.Exercise422
