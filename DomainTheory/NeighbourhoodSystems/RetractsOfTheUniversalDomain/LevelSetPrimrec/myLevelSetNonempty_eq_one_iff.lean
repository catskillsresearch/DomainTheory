module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myTestBit_eq_one_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.levelSetNonemptyBody
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myLevelSetNonempty

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.levelSet_nonempty_iff
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem myLevelSetNonempty_eq_one_iff (k m : ℕ) :
    myLevelSetNonempty k m = 1 ↔ (levelSet k m).Nonempty := by
  unfold myLevelSetNonempty
  rw [bExistsFn_eq_one_iff, levelSet_nonempty_iff]
  simp only [levelSetNonemptyBody, unpair_pair_fst, unpair_pair_snd, myTestBit_eq_one_iff]

end DomainTheory.NeighbourhoodSystems
