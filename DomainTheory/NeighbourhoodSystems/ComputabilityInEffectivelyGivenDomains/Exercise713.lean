/-ai
The system reconstructed from a computable presentation is isomorphic to the original neighbourhood system. The hint neighbourhood system of an inclusion structure is effectively given.

The numbered name example_713 is the conjunction of these statements. The proof is that conjunction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.reconstruct_isomorphic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.toSystem_isEffectivelyGiven

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise713

set_option linter.unusedVariables false

theorem example_713.{u_1} : And
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V),
    @DomainTheory.NeighbourhoodSystems.Isomorphic Nat α
      (@DomainTheory.NeighbourhoodSystems.Exercise713.reconstruct α V P) V)
  (∀ (I : DomainTheory.NeighbourhoodSystems.Exercise713.InclStructure),
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven Nat I.toSystem) :=
  @And.intro
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V),
    @DomainTheory.NeighbourhoodSystems.Isomorphic Nat α
      (@DomainTheory.NeighbourhoodSystems.Exercise713.reconstruct α V P) V)
  (∀ (I : DomainTheory.NeighbourhoodSystems.Exercise713.InclStructure),
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven Nat I.toSystem)
  (@DomainTheory.NeighbourhoodSystems.Exercise713.reconstruct_isomorphic)
  DomainTheory.NeighbourhoodSystems.Exercise713.InclStructure.toSystem_isEffectivelyGiven

end DomainTheory.NeighbourhoodSystems.Exercise713
