module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myDivPow2_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myModPow2

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem myModPow2_eq (m s : ℕ) : myModPow2 m s = m % 2 ^ s := by
  unfold myModPow2
  rw [myDivPow2_eq]
  have h : m / 2 ^ s * 2 ^ s + m % 2 ^ s = m := by
    rw [mul_comm]; exact Nat.div_add_mod m (2 ^ s)
  omega

end DomainTheory.NeighbourhoodSystems
