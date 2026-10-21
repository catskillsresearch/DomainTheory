/-ai
An index j lies in the hint neighbourhood of index n obtained from a computable presentation if and only if the j-th neighbourhood is contained in the n-th.

This is the defining membership condition, so the equivalence is definitional.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.InclStructure
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.toNbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.mem_toNbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.toSystem_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.ofPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.ofPresentation_INCL

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise713

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {V : NeighborhoodSystem α}

@[simp] theorem mem_ofPresentation_toNbhd (P : ComputablePresentation V) (j n : ℕ) :
    j ∈ (ofPresentation P).toNbhd n ↔ P.X j ⊆ P.X n := Iff.rfl

end DomainTheory.NeighbourhoodSystems.Exercise713
