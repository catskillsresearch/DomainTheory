module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise622.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

namespace Exercise619


/-- `Λ ∈ tok(Cone)`. -/
theorem nil_mem_Cone : ([] : Str) ∈ Cone.sys.master := rfl

end Exercise619
end DomainTheory.NeighbourhoodSystems
