module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.inclStructure

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise713
section
open NeighborhoodSystem

/-- Scott's Exercise 7.13: reconstructing from a presentation; inclusion structures are effectively given. -/
theorem example_713 :
    (∀ {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V),
      reconstruct P ≅ᴰ V) ∧
    (∀ (I : InclStructure), I.toSystem.IsEffectivelyGiven) :=
  ⟨@reconstruct_isomorphic, @InclStructure.toSystem_isEffectivelyGiven⟩
end
end DomainTheory.NeighbourhoodSystems.Exercise713

