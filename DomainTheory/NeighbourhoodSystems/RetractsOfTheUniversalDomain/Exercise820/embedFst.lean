module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u v

section Prod

variable {α : Type u} {β : Type v} (A : NeighborhoodSystem α) (B : NeighborhoodSystem β)

/-- **`a ↦ ⟨a, ⊥⟩`.** -/
noncomputable def embedFst : ApproximableMap A (prod A B) := paired (idMap A) (constMap A B.bot)

end Prod

end DomainTheory.NeighbourhoodSystems
