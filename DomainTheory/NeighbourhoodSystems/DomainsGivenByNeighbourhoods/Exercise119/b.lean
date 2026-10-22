/-ai
The neighbourhood b is the set consisting of the last two tokens.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise119.Tok

@[expose] public section

set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

/-- The neighbourhood `{1, 2}`. -/
def b : Set Tok := {1, 2}

end DomainTheory.NeighbourhoodSystems.Exercise119
