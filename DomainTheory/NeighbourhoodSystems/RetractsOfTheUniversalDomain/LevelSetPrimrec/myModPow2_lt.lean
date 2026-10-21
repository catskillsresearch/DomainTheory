/-ai
The derived remainder of m by two to the power s is strictly below that power.

Rewriting by the correctness of the remainder, it is the bound on a remainder modulo a
positive power of two.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myModPow2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myModPow2_eq

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem myModPow2_lt (m s : ℕ) : myModPow2 m s < 2 ^ s := by
  rw [myModPow2_eq]; exact Nat.mod_lt m (Nat.two_pow_pos s)

end DomainTheory.NeighbourhoodSystems
