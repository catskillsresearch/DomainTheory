module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.CoupledFixedPoints

@[expose] public section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap Exercise824

theorem exercise_8_24 {α : Type} {E : NeighborhoodSystem α}
    (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E))
    (hst : ∀ a b, FinitaryProjection a → FinitaryProjection b →
      FinitaryProjection (binOp s a b) ∧ FinitaryProjection (binOp t a b)) :
    FinitaryProjection (aStar s t) ∧ FinitaryProjection (bStar s t) :=
  isFinitaryProjection_aStar_bStar s t hst

end
