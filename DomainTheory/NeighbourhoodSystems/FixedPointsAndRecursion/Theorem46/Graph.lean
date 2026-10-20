module

public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem46.PeanoModel

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

universe u v

namespace PeanoModel

variable {M : Type u} {N : Type v}

/-- Scott's least fixed point `r ⊆ N × M`, realized as the inductively generated relation: the
least relation containing `(0, □)` and closed under `(n, m) ↦ (n⁺, m#)`. The two constructors are
Scott's facts (i) `0 r □` and (ii) `n r m ⟹ n⁺ r m#`. By Theorem 4.1 this *is* the least fixed
point of the approximable operator `u ↦ {(0,□)} ∪ {(n⁺,m#) ∣ (n,m) ∈ u}` on `P(N × M)`. -/
inductive Graph (P : PeanoModel M) (Q : PeanoModel N) : M → N → Prop
  | base : Graph P Q P.zero Q.zero
  | step : ∀ {m n}, Graph P Q m n → Graph P Q (P.succ m) (Q.succ n)

end PeanoModel
end DomainTheory.NeighbourhoodSystems
