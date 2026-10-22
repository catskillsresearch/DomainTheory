module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.levelSet_myUpsampleStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myUpsampleJointStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myUpsampleJointStep_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myUpsampleJointStep_iter_level

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem myUpsampleJointStep_iter_levelSet (k m d : ℕ) :
    levelSet (k + d) ((myUpsampleJointStep^[d] (Nat.pair k m)).unpair.2) = levelSet k m := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Function.iterate_succ_apply', myUpsampleJointStep_eq, unpair_pair_snd,
      myUpsampleJointStep_iter_level, show k + (d + 1) = (k + d) + 1 from by omega,
      levelSet_myUpsampleStep, ih]

end DomainTheory.NeighbourhoodSystems
