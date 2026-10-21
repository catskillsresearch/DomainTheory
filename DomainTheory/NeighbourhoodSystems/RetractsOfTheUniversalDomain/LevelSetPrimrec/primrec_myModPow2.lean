/-ai
Truncation to a power of two is primitive recursive. On a paired code it returns the first component minus the product of its iterated division by two to the power of the second component with that same power.

Two to the power of the right component and the iterated division are primitive recursive. Subtracting their product from the left component is primitive recursive, and that difference agrees with the truncation by reflexivity.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myDivPow2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.primrec_myDivPow2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myModPow2

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.V_no_minimal
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem primrec_myModPow2 : Nat.Primrec (fun t => myModPow2 t.unpair.1 t.unpair.2) := by
  have hpow : Nat.Primrec (fun t : ℕ => (2:ℕ) ^ t.unpair.2) := primrec_two_pow Nat.Primrec.right
  have hdiv : Nat.Primrec (fun t : ℕ => myDivPow2 t.unpair.1 t.unpair.2) := primrec_myDivPow2
  exact (primrec_sub₂ Nat.Primrec.left (primrec_mul₂ hdiv hpow)).of_eq fun t => rfl

end DomainTheory.NeighbourhoodSystems
