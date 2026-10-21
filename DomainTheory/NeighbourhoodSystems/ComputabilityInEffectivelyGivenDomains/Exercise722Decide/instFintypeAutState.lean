/-ai
The instance instFintypeAutState makes the automaton state type of an expression finite. The universal language has a one-point state type, a singleton word has an optional finite initial segment, an intersection has the product of the state types, and a concatenation has their sum, each finite by the standard instance after the recursive instances on the subexpressions.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Cat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Words
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.PathSplit
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.autState

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability

open Sum Set

variable {σ₁ σ₂ : Type}

instance instFintypeAutState : (e : SExpr) → Fintype (autState e)
  | .sigma => inferInstanceAs (Fintype Unit)
  | .single σ => inferInstanceAs (Fintype (Option (Fin (σ.length + 1))))
  | .cap a b => by
      letI := instFintypeAutState a; letI := instFintypeAutState b
      exact inferInstanceAs (Fintype (autState a × autState b))
  | .cat a b => by
      letI := instFintypeAutState a; letI := instFintypeAutState b
      exact inferInstanceAs (Fintype (autState a ⊕ autState b))

end Exercise722

end DomainTheory.NeighbourhoodSystems
