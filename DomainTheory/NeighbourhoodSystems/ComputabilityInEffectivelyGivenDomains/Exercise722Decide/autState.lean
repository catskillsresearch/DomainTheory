module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Cat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Words
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.PathSplit

@[expose] public section

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
