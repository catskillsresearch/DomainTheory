module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.effectiveIso812_UV
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_18

@[expose] public section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Exercise718

theorem exercise_8_12 :
    V.IsEffectivelyGiven ∧
      EffectivelyIsomorphic UComputablePresentation VComputablePresentation :=
  ⟨V.isEffectivelyGiven, ⟨effectiveIso812_UV⟩⟩

end
