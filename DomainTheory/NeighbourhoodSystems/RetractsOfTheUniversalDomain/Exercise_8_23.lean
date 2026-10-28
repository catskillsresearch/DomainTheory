module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.FixOp

@[expose] public section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap Exercise823

theorem exercise_8_23 {α : Type} {E : NeighborhoodSystem α}
    (t : ApproximableMap (funSpace E E) (funSpace E E))
    (ht : ∀ a, FinitaryProjection a → FinitaryProjection (tOp t a)) :
    FinitaryProjection (fixOp t) :=
  isFinitaryProjection_fixOp t ht

end
