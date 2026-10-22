module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myDivPow2_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myTestBit

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem myTestBit_eq_one_iff (m ℓ : ℕ) : myTestBit m ℓ = 1 ↔ m.testBit ℓ = true := by
  unfold myTestBit
  rw [myDivPow2_eq, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq]

end DomainTheory.NeighbourhoodSystems
