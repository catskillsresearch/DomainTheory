/-ai
The hint system is the neighbourhood system on the natural numbers whose neighbourhoods are the hint neighbourhoods, with master the set of all natural numbers. The master is the hint neighbourhood of the greatest code. If a hint neighbourhood is contained in an intersection of two others, the inclusion law gives a common lower index, and the meet index has hint neighbourhood equal to that intersection. Every neighbourhood is contained in the master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.InclStructure
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.toNbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.mem_toNbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.toNbhd_subset_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.toNbhd_top
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.toNbhd_inter_eq_iff

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise713

open NeighborhoodSystem Domain.Recursive

namespace InclStructure

variable (I : InclStructure)

/-- **Exercise 7.13 (⇐) — the hint system is a neighbourhood system.** `Sₙ = {m ∣ INCL(m, n)}` over
tokens `ℕ`, master `Δ = ℕ = S_{topIdx}`; closure under intersection is axiom (iv) via `MEET`. -/
def toSystem : NeighborhoodSystem ℕ where
  mem Y := ∃ n, Y = I.toNbhd n
  master := Set.univ
  master_nonempty := Set.univ_nonempty
  master_mem := ⟨I.topIdx, I.toNbhd_top.symm⟩
  inter_mem := by
    rintro X Y Z ⟨n, rfl⟩ ⟨m, rfl⟩ ⟨l, rfl⟩ hZsub
    have hln : I.INCL l n := I.toNbhd_subset_iff.mp (hZsub.trans Set.inter_subset_left)
    have hlm : I.INCL l m := I.toNbhd_subset_iff.mp (hZsub.trans Set.inter_subset_right)
    exact ⟨I.meetIdx n m, (I.toNbhd_inter_eq_iff n m (I.meetIdx n m)).mpr
      (I.meetIdx_spec ⟨l, hln, hlm⟩)⟩
  sub_master := by rintro X _; exact Set.subset_univ X

end InclStructure

end DomainTheory.NeighbourhoodSystems.Exercise713
