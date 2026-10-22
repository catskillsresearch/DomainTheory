/-ai
The right subtree of the binary tree is the set of tokens {1, 10, 11}, encoded as the three-element set {2, 5, 6}.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.Token

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example14

/-- The right subtree `{1, 10, 11} = {2, 5, 6}`. -/
def right : Set Token := {2, 5, 6}

end DomainTheory.NeighbourhoodSystems.Example14
