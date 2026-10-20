module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.InclStructure
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.toNbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.mem_toNbhd

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise713

open NeighborhoodSystem Domain.Recursive

namespace InclStructure

variable (I : InclStructure)

/-- `S_{topIdx} = ℕ`: the master code's neighbourhood is everything (axiom (iii)). -/
theorem toNbhd_top : I.toNbhd I.topIdx = Set.univ := by
  ext m
  simp only [mem_toNbhd, Set.mem_univ, iff_true]
  exact I.topIdx_spec m

end InclStructure

end DomainTheory.NeighbourhoodSystems.Exercise713
