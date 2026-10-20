module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myDivPow2

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- `myModPow2 m s = m % 2 ^ s`, derived from `myDivPow2` via `Nat.div_add_mod`
(`myModPow2_eq`): no separate general-purpose primitive-recursive `mod` is needed. -/
def myModPow2 (m s : ℕ) : ℕ := m - myDivPow2 m s * 2 ^ s

end DomainTheory.NeighbourhoodSystems
