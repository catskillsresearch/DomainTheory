module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823

@[expose] public section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap Exercise823

/-- **Exercise 8.23 (Scott 1981, PRG-19).** The fixed-point operator `fixOp t` is a finitary projection
when `t` preserves finitary projections. -/
theorem exercise_8_23 {α : Type} {E : NeighborhoodSystem α}
    (t : ApproximableMap (funSpace E E) (funSpace E E))
    (ht : ∀ a, FinitaryProjection a → FinitaryProjection (tOp t a)) :
    FinitaryProjection (fixOp t) :=
  isFinitaryProjection_fixOp t ht

end
