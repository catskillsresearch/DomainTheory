/-ai
The set represented by the union of two elements is the union of the sets they represent.

The numbered name example_220 is that statement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise220.toSet_unionMap

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise220

set_option linter.unusedVariables false

theorem example_220 : ∀
  (x y :
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
      DomainTheory.NeighbourhoodSystems.Exercise220.powerSet),
  @Eq (Set Nat)
    (DomainTheory.NeighbourhoodSystems.Exercise220.toSet
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap₂.toElementMap₂ Nat Nat Nat
        DomainTheory.NeighbourhoodSystems.Exercise220.powerSet DomainTheory.NeighbourhoodSystems.Exercise220.powerSet
        DomainTheory.NeighbourhoodSystems.Exercise220.powerSet DomainTheory.NeighbourhoodSystems.Exercise220.unionMap x
        y))
    (@Union.union (Set Nat) (@Set.instUnion Nat) (DomainTheory.NeighbourhoodSystems.Exercise220.toSet x)
      (DomainTheory.NeighbourhoodSystems.Exercise220.toSet y)) :=
  DomainTheory.NeighbourhoodSystems.Exercise220.toSet_unionMap

end DomainTheory.NeighbourhoodSystems.Exercise220
