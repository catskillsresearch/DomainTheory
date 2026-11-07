module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.ReflexiveDomain

@[expose] public section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.FixOp

theorem example_825 :
    (fixedNbhd (fixOp (tOpMap cCombinator)) ≅ᴰ
      funSpace (fixedNbhd (fixOp (tOpMap cCombinator)))
        (fixedNbhd (fixOp (tOpMap cCombinator)))) ∧
      (U ⊴ fixedNbhd (fixOp (tOpMap cCombinator))) :=
  ⟨exercise_8_25_main, exercise_8_25_universal⟩

