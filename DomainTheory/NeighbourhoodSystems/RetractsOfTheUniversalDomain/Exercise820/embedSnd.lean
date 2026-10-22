module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u v

section Prod

variable {α : Type u} {β : Type v} (A : NeighborhoodSystem α) (B : NeighborhoodSystem β)

/-- **`b ↦ ⟨⊥, b⟩`.** -/
noncomputable def embedSnd : ApproximableMap B (prod A B) := paired (constMap B A.bot) (idMap B)

end Prod

end DomainTheory.NeighbourhoodSystems
