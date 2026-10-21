/-ai
The function space of the one-point domain with itself is isomorphic to the one-point domain. The terminal domain is a fixed point of the function-space construction, which is why the obvious solution by retracts carries no information.

The numbered name example_825_unit is that statement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Unit.funSpace_unitSys_isomorphic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_825_unit : @DomainTheory.NeighbourhoodSystems.Isomorphic
  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Unit Unit DomainTheory.NeighbourhoodSystems.unitSys
    DomainTheory.NeighbourhoodSystems.unitSys)
  Unit
  (@DomainTheory.NeighbourhoodSystems.funSpace Unit Unit DomainTheory.NeighbourhoodSystems.unitSys
    DomainTheory.NeighbourhoodSystems.unitSys)
  DomainTheory.NeighbourhoodSystems.unitSys :=
  DomainTheory.NeighbourhoodSystems.funSpace_unitSys_isomorphic

end DomainTheory.NeighbourhoodSystems
