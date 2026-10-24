module

public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem46.PeanoModel
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem46.Graph

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

universe u v


namespace PeanoModel

variable {M : Type u} {N : Type v}


/-- **Inversion at `0` (uses 4.5(i)).** Anything related to `0` on the left is `□` on the right:
`0 r k ⟹ k = □`. (The other generating rule would force `0 = n⁺`, impossible by 4.5(i).) -/
theorem graph_zero_right (P : PeanoModel M) (Q : PeanoModel N) {k : N}
    (h : Graph P Q P.zero k) : k = Q.zero := by
  generalize hz : P.zero = z at h
  cases h with
  | base => rfl
  | step _ => exact absurd hz (P.zero_ne_succ _)

end PeanoModel
end DomainTheory.NeighbourhoodSystems
