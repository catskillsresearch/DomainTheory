module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Cat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Words
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.PathSplit
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.NFAinter
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.autState
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.instFintypeAutState
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.instDecidableEqAutState

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability

open Sum Set

variable {σ₁ σ₂ : Type}

/-- The uniform automaton for a fragment expression: leaves from `Exercise722DFA.lean`, `cap` by the
product construction, `cat` by the concatenation automaton (`Exercise722Cat.lean`). -/
def toNFA : (e : SExpr) → NFA Bool (autState e)
  | .sigma => sigmaDFA.toNFA
  | .single σ => (singleDFA σ).toNFA
  | .cap a b => NFAinter (toNFA a) (toNFA b)
  | .cat a b => (catEps (toNFA a) (toNFA b)).toNFA

end Exercise722

end DomainTheory.NeighbourhoodSystems
