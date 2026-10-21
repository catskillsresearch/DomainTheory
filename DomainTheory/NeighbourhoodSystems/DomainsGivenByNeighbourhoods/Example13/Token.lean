/-ai
The tokens of Scott's Example 1.3 are the three-element set {0, 1, 2}.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Example13

/-- Tokens for Example 1.3: `Δ = {0, 1, 2}`. -/
abbrev Token := Fin 3

end DomainTheory.NeighbourhoodSystems.Example13
