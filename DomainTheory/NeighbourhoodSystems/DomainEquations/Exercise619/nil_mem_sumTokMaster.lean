/-ai
The empty word belongs to the master of the concrete token sum.

It is the word inserted at the root of that master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.sumTokMaster

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example62 ExampleB

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

theorem nil_mem_sumTokMaster : ([] : Str) ∈ sumTokMaster D₀ D₁ := Set.mem_insert _ _

end Exercise619

end DomainTheory.NeighbourhoodSystems
