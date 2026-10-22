module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myLevelSetNonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myLevelSetNonempty_le_one
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myLevelSetNonempty_eq_one_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.canonIdx

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.V_no_minimal
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem canonIdx_eq_master_of_empty {c : ℕ} (h : levelSet c.unpair.1 c.unpair.2 = ∅) :
    canonIdx c = Nat.pair 0 1 := by
  unfold canonIdx
  have hle := myLevelSetNonempty_le_one c.unpair.1 c.unpair.2
  have hne1 : myLevelSetNonempty c.unpair.1 c.unpair.2 ≠ 1 := fun heq =>
    ((myLevelSetNonempty_eq_one_iff _ _).mp heq).ne_empty h
  have h0 : myLevelSetNonempty c.unpair.1 c.unpair.2 = 0 := by omega
  rw [h0, selectFn_zero]

end DomainTheory.NeighbourhoodSystems
