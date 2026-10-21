/-ai
The state type of a fragment expression is a single point for the full language, an optional length index for a singleton, a product of the state types for an intersection, and a sum of the state types for a concatenation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Cat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Words
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.PathSplit

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability

open Sum Set

variable {σ₁ σ₂ : Type}

/-- State type of the automaton for an `SExpr` (a `Fintype`, see `instFintypeAutState`). -/
def autState : SExpr → Type
  | .sigma => Unit
  | .single σ => Option (Fin (σ.length + 1))
  | .cap a b => autState a × autState b
  | .cat a b => autState a ⊕ autState b

end Exercise722

end DomainTheory.NeighbourhoodSystems
