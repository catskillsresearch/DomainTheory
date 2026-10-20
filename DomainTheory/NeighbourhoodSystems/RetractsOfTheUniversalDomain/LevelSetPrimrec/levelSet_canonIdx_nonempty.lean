module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.canonIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.canonIdx_eq_self_of_nonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.canonIdx_eq_master_of_empty

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- `canonIdx` always lands on a code presenting a non-empty `levelSet`. -/
theorem levelSet_canonIdx_nonempty (c : ℕ) :
    (levelSet (canonIdx c).unpair.1 (canonIdx c).unpair.2).Nonempty := by
  by_cases h : (levelSet c.unpair.1 c.unpair.2).Nonempty
  · rwa [canonIdx_eq_self_of_nonempty h]
  · rw [canonIdx_eq_master_of_empty (Set.not_nonempty_iff_eq_empty.mp h), unpair_pair_fst,
      unpair_pair_snd, levelSet_zero_one]
    exact Set.univ_nonempty

end DomainTheory.NeighbourhoodSystems
