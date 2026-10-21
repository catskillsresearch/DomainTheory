/-ai
The tokens of Example 1.4 are the seven nodes of the binary tree {Λ, 0, 1, 00, 01, 10, 11}, abbreviated as Fin 7, with Λ = 0, 0 = 1, 1 = 2, 00 = 3, 01 = 4, 10 = 5, and 11 = 6.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Example14

/-- Tokens for Example 1.4: the binary tree `Δ = {Λ,0,1,00,01,10,11}`, encoded as `Fin 7`
(`Λ=0, 0=1, 1=2, 00=3, 01=4, 10=5, 11=6`). -/
abbrev Token := Fin 7

end DomainTheory.NeighbourhoodSystems.Example14
