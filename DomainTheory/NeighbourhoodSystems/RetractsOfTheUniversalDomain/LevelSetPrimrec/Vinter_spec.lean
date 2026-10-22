module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.canonIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.canonIdx_eq_self_of_nonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.VX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.VX_canonIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.VinterRaw
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.levelSet_VinterRaw
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.Vcons_iff_nonempty_inter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.Vinter

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.V_no_minimal
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem Vinter_spec {n m : ℕ} (h : ∃ k, VX k ⊆ VX n ∩ VX m) : VX (Vinter n m) = VX n ∩ VX m := by
  have hne : (levelSet (VinterRaw n m).unpair.1 (VinterRaw n m).unpair.2).Nonempty := by
    rw [levelSet_VinterRaw]; exact (Vcons_iff_nonempty_inter n m).mp h
  unfold Vinter
  rw [VX_canonIdx]
  show levelSet (canonIdx (VinterRaw n m)).unpair.1 (canonIdx (VinterRaw n m)).unpair.2 = VX n ∩ VX m
  rw [canonIdx_eq_self_of_nonempty hne, levelSet_VinterRaw]

end DomainTheory.NeighbourhoodSystems
