/-ai
Every approximable map into the one-point domain equals the named terminal map.

The numbered name example_323 is that statement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise323.toUnit_unique

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_323.{u_1} : ∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
  (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α Unit V DomainTheory.NeighbourhoodSystems.unitSys),
  @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α Unit V DomainTheory.NeighbourhoodSystems.unitSys) f
    (@DomainTheory.NeighbourhoodSystems.toUnit α V) :=
  @DomainTheory.NeighbourhoodSystems.toUnit_unique

end DomainTheory.NeighbourhoodSystems
