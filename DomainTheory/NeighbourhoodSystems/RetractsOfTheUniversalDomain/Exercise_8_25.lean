module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.ReflexiveDomain

@[expose] public section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap Exercise823

/-- **Exercise 8.25 (Scott 1981, PRG-19).** A non-trivial domain `D ≅ D → D` containing `𝒰`. -/
theorem exercise_8_25 :
    (fixedNbhd (fixOp (tOpMap cCombinator)) ≅ᴰ
      funSpace (fixedNbhd (fixOp (tOpMap cCombinator)))
        (fixedNbhd (fixOp (tOpMap cCombinator)))) ∧
      (U ⊴ fixedNbhd (fixOp (tOpMap cCombinator))) :=
  ⟨exercise_8_25_main, exercise_8_25_universal⟩

end
