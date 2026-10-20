module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u v

section FunSpace

variable {α : Type u} {β : Type v} (A : NeighborhoodSystem α) (B : NeighborhoodSystem β)

/-- **`φ ↦ φ(⊥)`, evaluation at the bottom.** -/
noncomputable def evalBotMap : ApproximableMap (funSpace A B) B :=
  (evalMap A B).comp (paired (idMap (funSpace A B)) (constMap (funSpace A B) A.bot))

end FunSpace

end DomainTheory.NeighbourhoodSystems
