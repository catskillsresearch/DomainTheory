/-ai
The master neighbourhood is the set of all tokens.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise119.Tok

@[expose] public section

set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

/-- The master neighbourhood `Δ`. -/
def master : Set Tok := Set.univ

end DomainTheory.NeighbourhoodSystems.Exercise119
