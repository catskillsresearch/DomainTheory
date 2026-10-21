/-ai
The variables of a formula are the singleton of a variable, the empty set for falsehood or for truth, the variables of a negated formula, and the union of the variables of the two sides of a conjunction or of a disjunction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.Formula

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

/-- The (finite) set of variables occurring in a formula. -/
def vars : Formula → Finset ℕ
  | .var i => {i}
  | .bot => ∅
  | .top => ∅
  | .neg φ => vars φ
  | .and φ ψ => vars φ ∪ vars ψ
  | .or φ ψ => vars φ ∪ vars ψ

end DomainTheory.NeighbourhoodSystems
