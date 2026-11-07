module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.effectiveIso812_UV
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_18

@[expose] public section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem EffectiveIso

theorem example_812 :
    V.IsEffectivelyGiven ∧
      EffectivelyIsomorphic UComputablePresentation VComputablePresentation :=
  ⟨V.isEffectivelyGiven, ⟨effectiveIso812_UV⟩⟩

