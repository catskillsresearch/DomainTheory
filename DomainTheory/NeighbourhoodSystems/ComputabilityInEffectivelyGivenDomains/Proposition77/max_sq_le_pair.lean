module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

theorem max_sq_le_pair (i j : ℕ) : max i j * max i j ≤ Nat.pair i j := by
  unfold Nat.pair
  rcases lt_or_ge i j with h | h
  · rw [ite_eq_left h, show max i j = j by omega]; omega
  · rw [ite_eq_right (by omega), show max i j = i by omega]; omega

end Proposition77

end DomainTheory.NeighbourhoodSystems
