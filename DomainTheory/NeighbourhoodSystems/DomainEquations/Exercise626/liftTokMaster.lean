/-ai
The master neighbourhood of the lift is the empty string inserted into the false-bit embedding of the master of the original system.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {D : NeighborhoodSystem Str}

/-- The master neighbourhood `{Λ} ∪ 0Δ` of the lift. -/
def liftTokMaster (D : NeighborhoodSystem Str) : Set Str := insert [] (embBit false D.master)

end Exercise619

end DomainTheory.NeighbourhoodSystems
