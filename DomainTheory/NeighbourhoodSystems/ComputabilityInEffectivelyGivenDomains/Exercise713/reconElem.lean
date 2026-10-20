/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

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

/-- The element of the reconstructed system corresponding to `x ∈ |V|`: the filter
`{Sₙ ∣ Xₙ ∈ x}`. -/
def reconElem (P : ComputablePresentation V) (x : V.Element) : (reconstruct P).Element where
  mem Y := ∃ n, Y = (ofPresentation P).toNbhd n ∧ x.mem (P.X n)
  sub := by rintro Y ⟨n, rfl, _⟩; exact ⟨n, rfl⟩
  master_mem :=
    ⟨P.masterIdx, (ofPresentation P).toNbhd_top.symm, by rw [P.masterIdx_spec]; exact x.master_mem⟩
  inter_mem := by
    rintro X Y ⟨n, rfl, hxn⟩ ⟨m, rfl, hxm⟩
    have hmem : V.mem (P.X n ∩ P.X m) := x.sub (x.inter_mem hxn hxm)
    obtain ⟨q, hq⟩ := P.surj hmem
    refine ⟨q, ?_, ?_⟩
    · ext j
      rw [Set.mem_inter_iff, mem_ofPresentation_toNbhd, mem_ofPresentation_toNbhd,
        mem_ofPresentation_toNbhd, hq, Set.subset_inter_iff]
    · have : x.mem (P.X q) := by rw [hq]; exact x.inter_mem hxn hxm
      exact this
  up_mem := by
    rintro X Y ⟨n, rfl, hxn⟩ ⟨m, rfl⟩ hsub
    have hnm : P.X n ⊆ P.X m := (ofPresentation P).toNbhd_subset_iff.mp hsub
    exact ⟨m, rfl, x.up_mem hxn (P.mem_X m) hnm⟩

end DomainTheory.NeighbourhoodSystems.Exercise713
