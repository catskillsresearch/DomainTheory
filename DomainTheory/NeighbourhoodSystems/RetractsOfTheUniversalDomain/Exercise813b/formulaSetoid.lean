module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.Formula
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.SemanticEquiv

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

instance formulaSetoid : Setoid Formula where
  r := SemanticEquiv
  iseqv := ⟨fun _ _ => rfl, fun h v => (h v).symm, fun h1 h2 v => (h1 v).trans (h2 v)⟩

end DomainTheory.NeighbourhoodSystems
