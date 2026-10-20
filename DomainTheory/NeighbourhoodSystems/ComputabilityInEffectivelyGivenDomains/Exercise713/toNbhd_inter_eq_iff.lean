module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.InclStructure
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.MEET
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.toNbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.mem_toNbhd

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise713

open NeighborhoodSystem Domain.Recursive

namespace InclStructure

variable (I : InclStructure)

/-- `Sₙ ∩ Sₘ = Sₖ ↔ MEET(n, m, k)` — Scott's relation 7.1(i) *is* `MEET`. -/
theorem toNbhd_inter_eq_iff (n m k : ℕ) :
    I.toNbhd n ∩ I.toNbhd m = I.toNbhd k ↔ I.MEET n m k := by
  unfold MEET
  rw [Set.ext_iff]
  refine forall_congr' fun j => ?_
  rw [Set.mem_inter_iff, mem_toNbhd, mem_toNbhd, mem_toNbhd]
  exact iff_comm

end InclStructure

end DomainTheory.NeighbourhoodSystems.Exercise713
