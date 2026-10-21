/-ai
The inclusion relation read off a computable presentation holds of n and m if and only if the n-th neighbourhood is contained in the m-th.

This is the defining clause of that relation, so the equivalence is definitional.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.InclStructure
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.mem_toNbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.toSystem_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.ofPresentation

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise713

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {V : NeighborhoodSystem α}

@[simp] theorem ofPresentation_INCL (P : ComputablePresentation V) (n m : ℕ) :
    (ofPresentation P).INCL n m ↔ P.X n ⊆ P.X m := Iff.rfl

end DomainTheory.NeighbourhoodSystems.Exercise713
