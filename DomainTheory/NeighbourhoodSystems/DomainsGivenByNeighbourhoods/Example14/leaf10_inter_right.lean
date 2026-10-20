module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.right
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf10
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.right_inter_leaf10

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Example14

theorem leaf10_inter_right : leaf10 ∩ right = leaf10 := by
  rw [Set.inter_comm]; exact right_inter_leaf10

end DomainTheory.NeighbourhoodSystems.Example14
