module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.InclStructure
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.CONS
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.toNbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.mem_toNbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.toNbhd_subset_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.toNbhd_top
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.toNbhd_subset_inter_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.toNbhd_inter_eq_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.toSystem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.toSystem_mem

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise713

open NeighborhoodSystem Domain.Recursive

namespace InclStructure

variable (I : InclStructure)

/-- **Exercise 7.13 (⇐) — the hint system is effectively given.** The enumeration is `Sₙ`; relation
7.1(i) `Sₙ ∩ Sₘ = Sₖ` is `MEET` (`meet_dec`); relation 7.1(ii) consistency is `CONS` (`cons_dec`);
the intersection function is `meetIdx`; the master code is `topIdx`. -/
def toPresentation : ComputablePresentation I.toSystem where
  X := I.toNbhd
  mem_X n := ⟨n, rfl⟩
  surj := by rintro Y ⟨n, rfl⟩; exact ⟨n, rfl⟩
  interEq_computable :=
    RecDecidable.of_iff
      (fun t => (I.toNbhd_inter_eq_iff t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2))
      I.meet_dec
  cons_computable :=
    RecDecidable.of_iff
      (fun t => by
        refine exists_congr fun k => ?_
        exact I.toNbhd_subset_inter_iff k t.unpair.1 t.unpair.2)
      I.cons_dec
  inter := I.meetIdx
  inter_primrec := I.meetIdx_primrec
  inter_spec := by
    intro n m hcons
    obtain ⟨k, hk⟩ := hcons
    rw [Set.subset_inter_iff] at hk
    have hcons' : I.CONS n m := ⟨k, I.toNbhd_subset_iff.mp hk.1, I.toNbhd_subset_iff.mp hk.2⟩
    exact ((I.toNbhd_inter_eq_iff n m (I.meetIdx n m)).mpr (I.meetIdx_spec hcons')).symm
  masterIdx := I.topIdx
  masterIdx_spec := I.toNbhd_top

end InclStructure

end DomainTheory.NeighbourhoodSystems.Exercise713
