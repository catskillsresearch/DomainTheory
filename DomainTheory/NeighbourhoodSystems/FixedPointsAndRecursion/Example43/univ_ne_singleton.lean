/-ai
The whole space of natural numbers is not a singleton.

If it equalled the singleton of n, then n + 1 would belong to that singleton, contradicting that a successor differs from its argument.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Example43

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

/-- `ℕ` is not a singleton (a witness `n+1 ≠ n`). -/
theorem univ_ne_singleton (n : ℕ) : (Set.univ : Set ℕ) ≠ {n} := by
  intro h
  have h1 : (n + 1) ∈ ({n} : Set ℕ) := h ▸ Set.mem_univ (n + 1)
  exact Nat.succ_ne_self n h1

end DomainTheory.NeighbourhoodSystems.Example43
