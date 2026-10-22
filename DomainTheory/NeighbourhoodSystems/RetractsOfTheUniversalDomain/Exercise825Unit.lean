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
