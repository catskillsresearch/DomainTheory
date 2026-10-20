module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.VX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.VX_nonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.V_surj_VX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.VinterRaw
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.levelSet_VinterRaw

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **Scott's consistency condition reduces to non-emptiness.** -/
theorem Vcons_iff_nonempty_inter (n m : ℕ) :
    (∃ k, VX k ⊆ VX n ∩ VX m) ↔ (VX n ∩ VX m).Nonempty := by
  constructor
  · rintro ⟨k, hk⟩
    exact (VX_nonempty k).mono hk
  · intro hne
    rw [← levelSet_VinterRaw] at hne
    have hVmem : V.mem (VX n ∩ VX m) := by
      rw [← levelSet_VinterRaw]
      exact ⟨(VinterRaw n m).unpair.1, (VinterRaw n m).unpair.2, rfl, hne⟩
    obtain ⟨k, hk⟩ := V_surj_VX hVmem
    exact ⟨k, by rw [hk]⟩

end DomainTheory.NeighbourhoodSystems
