module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.canonIdx_eq_self_of_nonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.VX

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- `VX` is onto `V`'s neighbourhoods: every `V`-neighbourhood is already `levelSet k m` for some
non-empty pair `(k, m)`, on which `canonIdx` is a no-op. -/
theorem V_surj_VX : ∀ {Y : Set ℕ}, V.mem Y → ∃ n, VX n = Y := by
  rintro Y ⟨k, m, rfl, hne⟩
  refine ⟨Nat.pair k m, ?_⟩
  have hne' : (levelSet (Nat.pair k m).unpair.1 (Nat.pair k m).unpair.2).Nonempty := by
    rwa [unpair_pair_fst, unpair_pair_snd]
  unfold VX
  rw [canonIdx_eq_self_of_nonempty hne', unpair_pair_fst, unpair_pair_snd]

end DomainTheory.NeighbourhoodSystems
