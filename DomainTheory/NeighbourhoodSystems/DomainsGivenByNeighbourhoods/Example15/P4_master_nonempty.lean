/-ai
The master token set of Example 1.5 is nonempty.

The token 0 belongs to the set of all four tokens.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Basic.Countable.Defs
import all Mathlib.Basic.Countable.Defs
public import Mathlib.Data.Fintype.Powerset
import all Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example15.master

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example15

open NeighborhoodSystem

/-- The master token set itself is non-empty. -/
theorem P4_master_nonempty : master.Nonempty := by
  exact ⟨0, Set.mem_univ 0⟩

end DomainTheory.NeighbourhoodSystems.Example15
