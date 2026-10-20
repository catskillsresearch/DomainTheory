module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.canonList_fixed
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.decodeRatPair_masterPairCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.UX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.UX_eq

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- `UX` is onto `U`'s neighbourhoods: every `U`-neighbourhood already has a Scott-literal
presenting list (`U_mem_iff_scott`), on which `canonList` is a no-op (`canonList_fixed`). -/
theorem U_surj_UX : ∀ {Y : Set ℚ}, U.mem Y → ∃ n, UX n = Y := by
  intro Y hY
  obtain ⟨L, -, hYeq, -⟩ := U_mem_iff_scott.mp hY
  have hUL : U.mem (presentedIntervals L) := by rw [← hYeq]; exact hY
  exact ⟨encodeQPairList L, by
    rw [UX_eq, decodeQPairList_encodeQPairList, canonList_fixed hUL, ← hYeq]⟩

end DomainTheory.NeighbourhoodSystems
