/-ai
The master of the sum of the singleton solutions equals gTok of Gamma_D and Gamma_E.

The two sides are definitionally equal.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

namespace Exercise624

















/-- The master (token set) of `D + E` is `gTok Γ_D Γ_E`. -/
theorem master_Gsol : (Gsol Dsol Esol).sys.master = gTok GammaD GammaE := rfl

end Exercise624
end DomainTheory.NeighbourhoodSystems
