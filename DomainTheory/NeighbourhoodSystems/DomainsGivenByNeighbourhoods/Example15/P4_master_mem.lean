/-ai
The master neighbourhood of Example 1.5 is a neighbourhood.

Rewrite the master as the set of all four tokens, which is nonempty.
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
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example15.P4Mem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example15

open NeighborhoodSystem

/-- `Δ` is non-empty. -/
theorem P4_master_mem : P4Mem master := by
  rw [master]; exact Set.univ_nonempty

end DomainTheory.NeighbourhoodSystems.Example15
