/-ai
A set of the four tokens is a neighbourhood of Example 1.5 when it is nonempty.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Basic.Countable.Defs
import all Mathlib.Basic.Countable.Defs
public import Mathlib.Data.Fintype.Powerset
import all Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example15.Token

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Example15

open NeighborhoodSystem

/-- Membership: the non-empty subsets of `Δ`. -/
def P4Mem (X : Set Token) : Prop := X.Nonempty

end DomainTheory.NeighbourhoodSystems.Example15
