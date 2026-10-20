module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

/-- `a ≤ Nat.pair a b` (choice-free). -/
theorem le_pair_left (a b : ℕ) : a ≤ Nat.pair a b := by
  unfold Nat.pair; split <;> omega

end Proposition77

end DomainTheory.NeighbourhoodSystems
