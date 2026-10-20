module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise714
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_finGenSys
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_nbhdGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_SubD
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubD_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.toSubsystemSys
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.Q'X_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.Q'x_surj
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.masterCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.TreeVal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.TreeVal_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.Q2X
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.listToTreeAux
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.TreeVal_listToTreeAux
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubD

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

section UniversalSubsystem

section TreeVal2

variable (r : ℕ → ℕ) (x : (SubD UComputablePresentation).Element)

/-- **`surj` for `Q2X r`.** Every `D'x`-neighbourhood `Y` is some `Q2X r c` — reduce to the already-
proven list-based `Q'x_surj` (`Y = Q'X r n` for some `n`), then push `decodeList n` through
`listToTreeAux` and identify the result with `idxchain`'s own fold via `List.foldl_map`, so the same
`n` (repackaged as a tree code) also witnesses `Q2X r`. No fresh combinatorial work: this is a pure
bridging argument between the list-indexed and term-algebra-indexed enumerations of the *same*
underlying `Uinter`-folds. -/
theorem Q2x_surj (hspec : ∀ i, (toSubsystemSys UComputablePresentation x).mem (UX i) ↔ ∃ n, r n = i)
    {Y : Set ℚ} (hY : (toSubsystemSys UComputablePresentation x).mem Y) :
    ∃ c, Q2X r c = Y := by
  obtain ⟨n, hn⟩ := Q'x_surj r x hspec hY
  refine ⟨listToTreeAux masterCode (decodeList n), ?_⟩
  have hcode : (decodeList n).foldl (fun a j => Uinter a (r j)) UComputablePresentation.masterIdx
      = idxchain UComputablePresentation (List.map r (decodeList n)) := by
    unfold idxchain
    rw [List.foldl_map]
    rfl
  show UX (TreeVal r (listToTreeAux masterCode (decodeList n))) = Y
  rw [TreeVal_listToTreeAux, TreeVal_master, hcode, ← Q'X_eq]
  exact hn

end TreeVal2

end UniversalSubsystem

end DomainTheory.NeighbourhoodSystems
