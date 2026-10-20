module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

namespace Exercise624

/-- The first right-hand side `D + (D × E)`. -/
def Fsol (D E : ScottSys) : ScottSys := D.sum (D.prod E)

end Exercise624

end DomainTheory.NeighbourhoodSystems
