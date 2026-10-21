/-ai
The singleton-stack embedding of a domain into its infinite power sends an element to the stack with that element at the head and the bottom afterwards. It is the push composed with the pairing of the identity and the constant map at the bottom of the infinite power.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise618
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise511

variable {α : Type*} (V : NeighborhoodSystem α)

/-- The "singleton stack" embedding `D → D^∞`: `x ↦ ⟨x, ⊥, ⊥, …⟩`, i.e. `x` prepended to the all-`⊥`
stack. -/
def embedIntoPow : ApproximableMap V (iterSys V) :=
  (push V).comp (paired (idMap V) (constMap V (iterSys V).bot))

end DomainTheory.NeighbourhoodSystems
