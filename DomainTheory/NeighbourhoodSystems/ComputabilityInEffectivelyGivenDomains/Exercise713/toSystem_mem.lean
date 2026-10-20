module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.InclStructure
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.toNbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.mem_toNbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.toSystem

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise713

open NeighborhoodSystem Domain.Recursive

namespace InclStructure

variable (I : InclStructure)

@[simp] theorem toSystem_mem {Y : Set ℕ} : I.toSystem.mem Y ↔ ∃ n, Y = I.toNbhd n := Iff.rfl

end InclStructure

end DomainTheory.NeighbourhoodSystems.Exercise713
