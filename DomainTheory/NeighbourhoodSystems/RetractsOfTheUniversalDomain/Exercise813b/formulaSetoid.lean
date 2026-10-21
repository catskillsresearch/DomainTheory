/-ai
The setoid of formulas is semantic equivalence. It is reflexive because a truth value equals itself, symmetric because equality of truth values reverses, and transitive because equality of truth values composes, at each valuation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.Formula
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.SemanticEquiv

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

instance formulaSetoid : Setoid Formula where
  r := SemanticEquiv
  iseqv := ⟨fun _ _ => rfl, fun h v => (h v).symm, fun h1 h2 v => (h1 v).trans (h2 v)⟩

end DomainTheory.NeighbourhoodSystems
