module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.left
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf00
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.left_inter_leaf00

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Example14

theorem leaf00_inter_left : leaf00 ∩ left = leaf00 := by
  rw [Set.inter_comm]; exact left_inter_leaf00

end DomainTheory.NeighbourhoodSystems.Example14
