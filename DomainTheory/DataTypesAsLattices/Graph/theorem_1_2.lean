/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.Continuous
public import DomainTheory.DataTypesAsLattices.Graph.Basic
public import DomainTheory.DataTypesAsLattices.Graph.theorem_1_2_i
public import DomainTheory.DataTypesAsLattices.Graph.theorem_1_2_ii
public import DomainTheory.DataTypesAsLattices.Graph.theorem_1_2_iii

@[expose] public section


namespace DomainTheory.DataTypesAsLattices





/-- **Scott 1976, Theorem 1.2 (The graph theorem).** -/
theorem theorem_1_2 {f : Pomega → Pomega} (hf : IsScottContinuous f) (u : Pomega) :
    funOf (graph f) = f ∧ u ⊆ graph (funOf u) ∧
      (graph (funOf u) = u ↔ IsGraph u) :=
  ⟨theorem_1_2_i hf, theorem_1_2_ii u, theorem_1_2_iii u⟩

end DomainTheory.DataTypesAsLattices
