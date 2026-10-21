/-ai
An index m lies in the hint neighbourhood of an index n if and only if m is included in n.

This is the defining membership condition, so the equivalence is definitional.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.InclStructure
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.toNbhd

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise713

open NeighborhoodSystem Domain.Recursive

namespace InclStructure

variable (I : InclStructure)

@[simp] theorem mem_toNbhd {n m : ℕ} : m ∈ I.toNbhd n ↔ I.INCL m n := Iff.rfl

end InclStructure

end DomainTheory.NeighbourhoodSystems.Exercise713
