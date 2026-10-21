/-ai
There exist systems D and E such that D is a subsystem of D summed with the product of D and E, and E is a subsystem of the sum of D and E, simultaneously.

The numbered name example_624 is that statement.
ai-/
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
