module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.ClosureOperatorDomain

@[expose] public section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

/-- **Exercise 8.14 (Scott 1981, PRG-19).** The fixed-point set of a closure operator is a finitary domain. -/
theorem exercise_8_14 {α : Type*} {E : NeighborhoodSystem α} {a : ApproximableMap E E}
    (h : ClosureOperator a) : IsFinitary a :=
  isFinitary_of_isClosureOperator h

end
