module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.CoupledFixedPoints

@[expose] public section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap Exercise824

/-- **Exercise 8.24 (Scott 1981, PRG-19).** The coupled fixed-point projections `a★`, `b★` are finitary. -/
theorem exercise_8_24 {α : Type} {E : NeighborhoodSystem α}
    (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E))
    (hst : ∀ a b, FinitaryProjection a → FinitaryProjection b →
      FinitaryProjection (binOp s a b) ∧ FinitaryProjection (binOp t a b)) :
    FinitaryProjection (aStar s t) ∧ FinitaryProjection (bStar s t) :=
  isFinitaryProjection_aStar_bStar s t hst

end
