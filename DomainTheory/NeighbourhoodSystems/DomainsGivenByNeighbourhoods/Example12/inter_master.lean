module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.Token
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.master

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Example12

theorem inter_master (A : Set Token) : A ∩ master = A := by
  rw [master]; exact Set.inter_univ A

end DomainTheory.NeighbourhoodSystems.Example12
