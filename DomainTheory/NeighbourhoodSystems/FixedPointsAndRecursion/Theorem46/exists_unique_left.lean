module

public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem46.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem46.Graphu2eswap
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem46.exists_unique_right

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

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
end DomainTheory.NeighbourhoodSystems
