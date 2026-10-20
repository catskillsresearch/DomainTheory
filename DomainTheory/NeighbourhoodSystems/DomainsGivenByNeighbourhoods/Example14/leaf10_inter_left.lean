module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.Token
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.left
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf10
import all DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.left_inter_leaf10

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Example14

theorem leaf10_inter_left : leaf10 ∩ left = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact left_inter_leaf10

end DomainTheory.NeighbourhoodSystems.Example14
