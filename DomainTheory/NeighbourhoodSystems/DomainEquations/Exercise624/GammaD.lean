/-ai
The first component Gamma_D of the double fixed point is the union, over all stages, of the first coordinate of the pair iteration.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.pIter

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

namespace Exercise624

/-- The first component of the double fixed point, `Γ_D = ⋃ₙ (Φⁿ).₁`. -/
def GammaD : Set Str := ⋃ n, (pIter n).1

end Exercise624

end DomainTheory.NeighbourhoodSystems
