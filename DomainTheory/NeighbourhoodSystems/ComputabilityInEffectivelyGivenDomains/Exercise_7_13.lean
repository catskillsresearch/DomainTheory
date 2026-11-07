module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.inclStructure

@[expose] public section

open DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem
open DomainTheory.NeighbourhoodSystems.InclStructure
/-- Scott's Exercise 7.13: reconstructing from a presentation; inclusion structures are effectively given. -/
theorem example_713 :
    (∀ {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V),
      reconstruct P ≅ᴰ V) ∧
    (∀ (I : InclStructure), I.toSystem.IsEffectivelyGiven) :=
  ⟨@reconstruct_isomorphic, @InclStructure.toSystem_isEffectivelyGiven⟩

