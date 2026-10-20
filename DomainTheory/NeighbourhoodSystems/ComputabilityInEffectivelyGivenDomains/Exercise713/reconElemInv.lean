module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.InclStructure
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.toNbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.mem_toNbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.toNbhd_subset_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.toNbhd_top
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.toSystem_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.ofPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.ofPresentation_INCL
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.mem_ofPresentation_toNbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.reconstruct

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise713

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {V : NeighborhoodSystem α}

/-- The element of `|V|` corresponding to `y` in the reconstructed system: the filter
`{Xₙ ∣ Sₙ ∈ y}`. -/
def reconElemInv (P : ComputablePresentation V) (y : (reconstruct P).Element) : V.Element where
  mem W := ∃ n, W = P.X n ∧ y.mem ((ofPresentation P).toNbhd n)
  sub := by rintro W ⟨n, rfl, _⟩; exact P.mem_X n
  master_mem :=
    ⟨P.masterIdx, P.masterIdx_spec.symm, by
      rw [show (ofPresentation P).toNbhd P.masterIdx = Set.univ from (ofPresentation P).toNbhd_top]
      exact y.master_mem⟩
  inter_mem := by
    rintro X Y ⟨n, rfl, hyn⟩ ⟨m, rfl, hym⟩
    obtain ⟨p, hp⟩ := y.sub (y.inter_mem hyn hym)
    have hpmem : p ∈ (ofPresentation P).toNbhd n ∩ (ofPresentation P).toNbhd m :=
      hp ▸ ((ofPresentation P).mem_toNbhd.mpr ((ofPresentation P).incl_refl p))
    rw [Set.mem_inter_iff, mem_ofPresentation_toNbhd, mem_ofPresentation_toNbhd] at hpmem
    have hwit : P.X p ⊆ P.X n ∩ P.X m := Set.subset_inter hpmem.1 hpmem.2
    have hmem : V.mem (P.X n ∩ P.X m) := V.inter_mem (P.mem_X n) (P.mem_X m) (P.mem_X p) hwit
    obtain ⟨q, hq⟩ := P.surj hmem
    refine ⟨q, hq.symm, ?_⟩
    have htoNbhd : (ofPresentation P).toNbhd q
        = (ofPresentation P).toNbhd n ∩ (ofPresentation P).toNbhd m := by
      ext j
      rw [Set.mem_inter_iff, mem_ofPresentation_toNbhd, mem_ofPresentation_toNbhd,
        mem_ofPresentation_toNbhd, hq, Set.subset_inter_iff]
    rw [htoNbhd]
    exact y.inter_mem hyn hym
  up_mem := by
    rintro W Z ⟨n, rfl, hyn⟩ hZ hWZ
    obtain ⟨p, hp⟩ := P.surj hZ
    refine ⟨p, hp.symm, ?_⟩
    have hnp : (ofPresentation P).toNbhd n ⊆ (ofPresentation P).toNbhd p :=
      (ofPresentation P).toNbhd_subset_iff.mpr (by show P.X n ⊆ P.X p; rw [hp]; exact hWZ)
    exact y.up_mem hyn ⟨p, rfl⟩ hnp

end DomainTheory.NeighbourhoodSystems.Exercise713
