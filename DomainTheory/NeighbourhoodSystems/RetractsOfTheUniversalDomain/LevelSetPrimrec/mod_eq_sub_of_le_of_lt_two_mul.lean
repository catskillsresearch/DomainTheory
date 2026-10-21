/-ai
If s is at most j and j is strictly below twice s, then the remainder of j modulo s
equals j minus s.

Then j equals the sum of j minus s and s, by arithmetic. The remainder is unchanged by
that rewriting, adding s on the right does not change the remainder, and the difference
is strictly below s by arithmetic, so the remainder is the difference.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- `j % s = j - s` when `s ≤ j < 2 * s` (the single-wraparound case of `%`). -/
theorem mod_eq_sub_of_le_of_lt_two_mul {j s : ℕ} (h1 : s ≤ j) (h2 : j < 2 * s) :
    j % s = j - s := by
  have heq : j = (j - s) + s := by omega
  calc j % s = ((j - s) + s) % s := by rw [← heq]
    _ = (j - s) % s := Nat.add_mod_right _ _
    _ = j - s := Nat.mod_eq_of_lt (by omega)

end DomainTheory.NeighbourhoodSystems
