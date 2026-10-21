/-ai
If the languages of a and of b both lie in S, then consistentB a b is true if and only if the intersection of those languages lies in S.

The numbered name example_722_decide is that statement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.consistentB_iff_Ssys

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise722

set_option linter.unusedVariables false

theorem example_722_decide : ∀ (a b : DomainTheory.NeighbourhoodSystems.Exercise722.SExpr),
  DomainTheory.NeighbourhoodSystems.Exercise722.InS (DomainTheory.NeighbourhoodSystems.Exercise722.denote a) →
    DomainTheory.NeighbourhoodSystems.Exercise722.InS (DomainTheory.NeighbourhoodSystems.Exercise722.denote b) →
      Iff (@Eq Bool (DomainTheory.NeighbourhoodSystems.Exercise722.consistentB a b) Bool.true)
        (DomainTheory.NeighbourhoodSystems.Exercise722.InS
          (@Inter.inter (Set (List Bool)) (@Set.instInter (List Bool))
            (DomainTheory.NeighbourhoodSystems.Exercise722.denote a)
            (DomainTheory.NeighbourhoodSystems.Exercise722.denote b))) :=
  DomainTheory.NeighbourhoodSystems.Exercise722.consistentB_iff_Ssys

end DomainTheory.NeighbourhoodSystems.Exercise722
