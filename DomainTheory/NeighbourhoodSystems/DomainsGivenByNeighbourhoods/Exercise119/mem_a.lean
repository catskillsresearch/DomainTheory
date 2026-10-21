/-ai
The neighbourhood of the first two tokens is a neighbourhood.

The classification of neighbourhoods supplies the disjunct that identifies this set with itself.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise119.a
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise119.mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise119.mem_iff

@[expose] public section

set_option linter.unusedSectionVars false

set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

theorem mem_a : mem a := (mem_iff _).mpr (Or.inr (Or.inl rfl))

end DomainTheory.NeighbourhoodSystems.Exercise119
