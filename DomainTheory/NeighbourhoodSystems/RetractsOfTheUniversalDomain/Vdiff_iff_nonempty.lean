/-ai
An enumerated neighbourhood of V equals the difference of two enumerated neighbourhoods if and only if that difference is nonempty.

A representing neighbourhood is nonempty. If the difference is nonempty, the level set of the raw difference is nonempty, so the difference is a neighbourhood of V presented by that raw level and mask, and surjectivity supplies an index.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.VdiffRaw
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.levelSet_VdiffRaw

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **Scott's consistency condition for `\` reduces to non-emptiness**, mirroring
`Vcons_iff_nonempty_inter`. -/
theorem Vdiff_iff_nonempty (n m : ℕ) :
    (∃ k, VX k = VX n \ VX m) ↔ (VX n \ VX m).Nonempty := by
  constructor
  · rintro ⟨k, hk⟩
    rw [← hk]; exact VX_nonempty k
  · intro hne
    rw [← levelSet_VdiffRaw] at hne
    have hVmem : V.mem (VX n \ VX m) := by
      rw [← levelSet_VdiffRaw]
      exact ⟨(VdiffRaw n m).unpair.1, (VdiffRaw n m).unpair.2, rfl, hne⟩
    obtain ⟨k, hk⟩ := V_surj_VX hVmem
    exact ⟨k, hk⟩

end DomainTheory.NeighbourhoodSystems
