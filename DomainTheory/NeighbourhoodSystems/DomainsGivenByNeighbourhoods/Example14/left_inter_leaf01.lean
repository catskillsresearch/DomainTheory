module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.left
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf01

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Example14

theorem left_inter_leaf01 : left ∩ leaf01 = leaf01 := by
  ext t; fin_cases t <;> simp [left, leaf01]

end DomainTheory.NeighbourhoodSystems.Example14
