module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.effectiveIso812_UV
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_18

@[expose] public section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Exercise718

/-- **Exercise 8.12 (Scott 1981, PRG-19).** `V` is effectively given and effectively isomorphic
to `U`, hence another presentation of `U`. --/
theorem exercise_8_12 :
    V.IsEffectivelyGiven ∧
      EffectivelyIsomorphic UComputablePresentation VComputablePresentation :=
  ⟨V_isEffectivelyGiven, ⟨effectiveIso812_UV⟩⟩

end
