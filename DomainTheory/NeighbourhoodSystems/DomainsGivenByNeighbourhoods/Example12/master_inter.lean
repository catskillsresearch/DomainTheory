module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.Token
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.master

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Example12

theorem master_inter (A : Set Token) : master ∩ A = A := by
  rw [master]; exact Set.univ_inter A

end DomainTheory.NeighbourhoodSystems.Example12
