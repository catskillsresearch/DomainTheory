/-ai
If the successor of an element m is related by the graph to k, then m is related to some element whose successor is k.

The successor of m is generalized to a variable and the generating relation is split into cases. The base constructor would identify that successor with zero, which is excluded. The step constructor supplies a predecessor pair, and injectivity of the successor identifies the left-hand predecessor with m.
ai-/
module

public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem46.Basic

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
