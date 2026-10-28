module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.ClosureOperatorDomain

@[expose] public section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

theorem exercise_8_14 {α : Type*} {E : NeighborhoodSystem α} {a : ApproximableMap E E}
    (h : ClosureOperator a) : IsFinitary a :=
  isFinitary_of_isClosureOperator h

end
