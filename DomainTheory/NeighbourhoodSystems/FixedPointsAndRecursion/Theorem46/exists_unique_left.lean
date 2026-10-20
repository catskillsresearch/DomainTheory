/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.Neighborhood.Theorem46.Basic
public import DomainTheory.Neighborhood.Theorem46.Graphu2eswap
public import DomainTheory.Neighborhood.Theorem46.exists_unique_right

@[expose] public section


namespace DomainTheory.Neighborhood

universe u v


namespace PeanoModel

variable {M : Type u} {N : Type v}


/-- Dually (by `Graph.swap`), each element of the right model is related to exactly one element of
the left model. -/
theorem exists_unique_left (P : PeanoModel M) (Q : PeanoModel N) (n : N) :
    ∃! m, Graph P Q m n := by
  obtain ⟨m, hm, huniq⟩ := exists_unique_right Q P n
  exact ⟨m, hm.swap, fun y hy => huniq y hy.swap⟩

end PeanoModel
end DomainTheory.Neighborhood
