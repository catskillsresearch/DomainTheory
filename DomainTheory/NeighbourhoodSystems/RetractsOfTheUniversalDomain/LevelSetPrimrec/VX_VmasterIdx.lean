module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.canonIdx_eq_self_of_nonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.VX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.VmasterIdx

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem VX_VmasterIdx : VX VmasterIdx = V.master := by
  have hne : (levelSet (Nat.pair 0 1 : ℕ).unpair.1 (Nat.pair 0 1 : ℕ).unpair.2).Nonempty := by
    rw [unpair_pair_fst, unpair_pair_snd, levelSet_zero_one]; exact Set.univ_nonempty
  unfold VX VmasterIdx
  rw [canonIdx_eq_self_of_nonempty hne, unpair_pair_fst, unpair_pair_snd, levelSet_zero_one]
  rfl

end DomainTheory.NeighbourhoodSystems
