module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.VdiffRaw
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.levelSet_VdiffRaw
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Vdiff

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem Vdiff_spec {n m : ℕ} (h : ∃ k, VX k = VX n \ VX m) : VX (Vdiff n m) = VX n \ VX m := by
  have hne : (levelSet (VdiffRaw n m).unpair.1 (VdiffRaw n m).unpair.2).Nonempty := by
    rw [levelSet_VdiffRaw]; obtain ⟨k, hk⟩ := h; rw [← hk]; exact VX_nonempty k
  unfold Vdiff
  rw [VX_canonIdx]
  show levelSet (canonIdx (VdiffRaw n m)).unpair.1 (canonIdx (VdiffRaw n m)).unpair.2 = VX n \ VX m
  rw [canonIdx_eq_self_of_nonempty hne, levelSet_VdiffRaw]

end DomainTheory.NeighbourhoodSystems
