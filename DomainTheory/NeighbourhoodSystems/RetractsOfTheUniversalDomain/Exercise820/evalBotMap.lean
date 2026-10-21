/-ai
Evaluation at bottom sends a function from A to B to its value at the bottom of A. It is the evaluation map composed with the pairing of the identity and the constant map at that bottom.
ai-/
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
