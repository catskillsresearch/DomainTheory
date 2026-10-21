/-ai
The second component Gamma_E of the double fixed point is the union, over all stages, of the second coordinate of the pair iteration.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.pIter

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

namespace Exercise624

/-- The second component of the double fixed point, `Γ_E = ⋃ₙ (Φⁿ).₂`. -/
def GammaE : Set Str := ⋃ n, (pIter n).2

end Exercise624

end DomainTheory.NeighbourhoodSystems
