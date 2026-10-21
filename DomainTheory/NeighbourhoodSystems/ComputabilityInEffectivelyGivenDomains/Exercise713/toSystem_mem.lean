/-ai
A set of natural numbers is a neighbourhood of the hint system if and only if it equals the hint neighbourhood of some index.

This is the defining membership condition, so the equivalence is definitional.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.InclStructure
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.toNbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.mem_toNbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.toSystem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise713

open NeighborhoodSystem Domain.Recursive

namespace InclStructure

variable (I : InclStructure)

@[simp] theorem toSystem_mem {Y : Set ℕ} : I.toSystem.mem Y ↔ ∃ n, Y = I.toNbhd n := Iff.rfl

end InclStructure

end DomainTheory.NeighbourhoodSystems.Exercise713
