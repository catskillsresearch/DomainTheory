/-ai
The hint neighbourhood system of an inclusion structure is effectively given.

Its computable presentation is a witness.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise713

open NeighborhoodSystem Domain.Recursive


namespace InclStructure

variable (I : InclStructure)


/-- **Exercise 7.13 (⇐).** The hint system is effectively given. -/
theorem toSystem_isEffectivelyGiven : I.toSystem.IsEffectivelyGiven := ⟨I.toPresentation⟩

end InclStructure
end DomainTheory.NeighbourhoodSystems.Exercise713
