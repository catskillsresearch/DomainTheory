module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819

@[expose] public section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap Exercise326

universe u

/-- **Exercise 8.19 (Scott 1981, PRG-19).** If `T ⊴ E` and `E → E ⊴ E`, then `E+E ⊴ E` and `E×E ⊴ E`. -/
theorem exercise_8_19 {α : Type u} {E : NeighborhoodSystem α}
    (hE : ∀ X, E.mem X → X.Nonempty) (hT : TD ⊴ E) (hArrow : funSpace E E ⊴ E) :
    sum E E hE hE ⊴ E ∧ prod E E ⊴ E :=
  exercise_8_19_assembly hE hT hArrow

end
