module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv.interEqB_iff

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise722

set_option linter.unusedVariables false

theorem example_722_equiv : ∀ (e1 e2 : DomainTheory.NeighbourhoodSystems.Exercise722.SExpr),
  Iff (@Eq Bool (DomainTheory.NeighbourhoodSystems.Exercise722.interEqB e1 e2) Bool.true)
    (@Eq (Set (List Bool)) (DomainTheory.NeighbourhoodSystems.Exercise722.denote e1)
      (DomainTheory.NeighbourhoodSystems.Exercise722.denote e2)) :=
  DomainTheory.NeighbourhoodSystems.Exercise722.interEqB_iff

end DomainTheory.NeighbourhoodSystems.Exercise722
