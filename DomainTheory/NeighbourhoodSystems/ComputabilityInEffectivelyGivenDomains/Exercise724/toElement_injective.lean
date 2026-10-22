module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.LFunData
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.BasicInst2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.cons_inl
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.cons_inr
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.L_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.L_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.finPrefix_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.streamElement
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.toElement
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.principal_hasMin
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.streamElement_not_hasMin
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.streamElement_injective

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise724

open NeighborhoodSystem Domain.Recursive

/-- **`toElement` is injective** (Exercise 7.24, second claim, uniqueness half). Finite vs. finite
is `nbhd_injective`; the two mixed cases are separated by `HasMin`; infinite vs. infinite is
`streamElement_injective`. -/
theorem toElement_injective : Function.Injective toElement := by
  rintro (l₁ | f₁) (l₂ | f₂) heq
  · exact congrArg Sum.inl
      (nbhd_injective (principal_injective (V := L) (mem_nbhd l₁) (mem_nbhd l₂) heq))
  · have heq' : L.principal (mem_nbhd l₁) = streamElement f₂ := heq
    exact absurd (heq' ▸ principal_hasMin l₁) (streamElement_not_hasMin f₂)
  · have heq' : streamElement f₁ = L.principal (mem_nbhd l₂) := heq
    exact absurd (principal_hasMin l₂) (heq' ▸ streamElement_not_hasMin f₁)
  · exact congrArg Sum.inr (streamElement_injective heq)

end DomainTheory.NeighbourhoodSystems.Exercise724
