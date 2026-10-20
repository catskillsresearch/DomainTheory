module

public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem46.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem46.graph_zero_right
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem46.graph_succ_right

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

universe u v


namespace PeanoModel

variable {M : Type u} {N : Type v}


/-- Each element of the left model is related by `Graph` to exactly one element of the right
model. Proved by the induction principle 4.5(iii) on the set `{m ∣ ∃! n, m r n}`: the base case
is the `0`-inversion `graph_zero_right`, the step case the successor-inversion `graph_succ_right`
together with 4.5(ii). -/
theorem exists_unique_right (P : PeanoModel M) (Q : PeanoModel N) (m : M) :
    ∃! n, Graph P Q m n := by
  refine P.induction {m | ∃! n, Graph P Q m n} ?_ ?_ m
  · exact ⟨Q.zero, Graph.base, fun k hk => graph_zero_right P Q hk⟩
  · rintro m' ⟨n', hn', huniq⟩
    refine ⟨Q.succ n', Graph.step hn', fun k hk => ?_⟩
    obtain ⟨n'', hn'', rfl⟩ := graph_succ_right P Q hk
    rw [huniq n'' hn'']

end PeanoModel
end DomainTheory.NeighbourhoodSystems
