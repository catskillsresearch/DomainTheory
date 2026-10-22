module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.exists_simultaneous_subsystems

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise624

set_option linter.unusedVariables false

theorem example_624 : ∃ (D : DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys) (E :
  DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys),
  And
    (@DomainTheory.NeighbourhoodSystems.Subsystem DomainTheory.NeighbourhoodSystems.ExampleB.Str D.sys
      (D.sum (D.prod E)).sys)
    (@DomainTheory.NeighbourhoodSystems.Subsystem DomainTheory.NeighbourhoodSystems.ExampleB.Str E.sys (D.sum E).sys) :=
  DomainTheory.NeighbourhoodSystems.Exercise624.exists_simultaneous_subsystems

end DomainTheory.NeighbourhoodSystems.Exercise624
