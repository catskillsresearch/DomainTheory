/-ai
The master neighbourhood of the concrete token sum is the empty word together with the false-tagged copy of the master of the first system and the true-tagged copy of the master of the second.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example62 ExampleB

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

/-- The master neighbourhood `{Λ} ∪ 0Δ₀ ∪ 1Δ₁` of the concrete sum. -/
def sumTokMaster (D₀ D₁ : NeighborhoodSystem Str) : Set Str :=
  insert [] (embBit false D₀.master ∪ embBit true D₁.master)

end Exercise619

end DomainTheory.NeighbourhoodSystems
