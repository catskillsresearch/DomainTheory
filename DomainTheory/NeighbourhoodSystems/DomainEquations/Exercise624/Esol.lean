/-ai
The solution system E is the singleton neighbourhood system on the token set Gamma_E, which contains the empty string.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.GammaE
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.nil_mem_GammaE

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

namespace Exercise624

/-- The solution system `E = {Γ_E}`. -/
def Esol : ScottSys := singletonSys GammaE ⟨[], nil_mem_GammaE⟩

end Exercise624

end DomainTheory.NeighbourhoodSystems
