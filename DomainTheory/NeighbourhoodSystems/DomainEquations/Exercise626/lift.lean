/-ai
The lift of a Scott system is the Scott system whose neighbourhood system is the tokenwise lift of its underlying system, using that the system is empty-free.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.liftTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.liftTok_nonempty

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {D : NeighborhoodSystem Str}

/-- The **lift object** `𝒟_⊥` of Scott's category. -/
def ScottSys.lift (A : ScottSys) : ScottSys := ⟨liftTok A.sys A.ne, liftTok_nonempty A.ne⟩

end Exercise619

end DomainTheory.NeighbourhoodSystems
