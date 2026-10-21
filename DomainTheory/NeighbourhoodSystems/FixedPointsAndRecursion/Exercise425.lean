/-ai
The map from the flat naturals sends bottom to the bottom of the unary sequence system.

The numbered name example_425 is that statement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.relateNToC1_bot

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise425

set_option linter.unusedVariables false

theorem example_425 : @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat DomainTheory.NeighbourhoodSystems.Exercise425.C1)
  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Nat Nat DomainTheory.NeighbourhoodSystems.Example43.N
    DomainTheory.NeighbourhoodSystems.Exercise425.C1 DomainTheory.NeighbourhoodSystems.Exercise425.relateNToC1
    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot Nat DomainTheory.NeighbourhoodSystems.Example43.N))
  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot Nat DomainTheory.NeighbourhoodSystems.Exercise425.C1) :=
  DomainTheory.NeighbourhoodSystems.Exercise425.relateNToC1_bot

end DomainTheory.NeighbourhoodSystems.Exercise425
