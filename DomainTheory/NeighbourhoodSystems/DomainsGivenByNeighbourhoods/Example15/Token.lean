/-ai
The tokens of Scott's Example 1.5 are the four-element set {0, 1, 2, 3}.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example15

open NeighborhoodSystem

/-- Tokens for Example 1.5: `Δ = {0, 1, 2, 3}`. -/
abbrev Token := Fin 4

end DomainTheory.NeighbourhoodSystems.Example15
