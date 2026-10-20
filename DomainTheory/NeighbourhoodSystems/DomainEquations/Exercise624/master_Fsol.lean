module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise624.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

namespace Exercise624

















/-- The master (token set) of `D + (D×E)` is `fTok Γ_D Γ_E` — definitionally, the sum/product
masters expand to the tagged-union shape `gTok`/`fTok`. -/
theorem master_Fsol : (Fsol Dsol Esol).sys.master = fTok GammaD GammaE := rfl

end Exercise624
end DomainTheory.NeighbourhoodSystems
