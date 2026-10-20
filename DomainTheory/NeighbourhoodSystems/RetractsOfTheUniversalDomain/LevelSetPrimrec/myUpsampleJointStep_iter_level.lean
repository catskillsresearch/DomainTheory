module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myUpsampleJointStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myUpsampleJointStep_eq

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- Iterate `myUpsampleJointStep` `d` times from `pair k m`, and read off the level after `d`
steps and the resulting mask. -/
theorem myUpsampleJointStep_iter_level (k m d : ℕ) :
    (myUpsampleJointStep^[d] (Nat.pair k m)).unpair.1 = k + d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Function.iterate_succ_apply', myUpsampleJointStep_eq, unpair_pair_fst, ih]
    omega

end DomainTheory.NeighbourhoodSystems
