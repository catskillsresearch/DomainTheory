module

public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem46.PeanoModel
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem46.Graph

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

universe u v


namespace PeanoModel

variable {M : Type u} {N : Type v}


/-- **Inversion at a successor (uses 4.5(i)/(ii)).** Anything related to `n⁺` on the left comes
from a relation `n r n₀` with right value a successor: `n⁺ r k ⟹ ∃ n₀, n r n₀ ∧ k = n₀#`. -/
theorem graph_succ_right (P : PeanoModel M) (Q : PeanoModel N) {m : M} {k : N}
    (h : Graph P Q (P.succ m) k) : ∃ n, Graph P Q m n ∧ k = Q.succ n := by
  generalize hz : P.succ m = z at h
  cases h with
  | base => exact absurd hz.symm (P.zero_ne_succ _)
  | step h' =>
    rename_i m0 n0
    have hm : m = m0 := P.succ_injective hz
    subst hm
    exact ⟨n0, h', rfl⟩

end PeanoModel
end DomainTheory.NeighbourhoodSystems
