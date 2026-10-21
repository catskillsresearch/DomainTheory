/-ai
The master neighbourhood of Example 1.3 is not contained in {2}.

The token 0 belongs to the master. Containment would put it in {2}.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.Token
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.two

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Example13

theorem master_not_subset_two : ¬master ⊆ two := by
  intro h
  have : (0 : Token) ∈ two := h (by simp [master])
  simp [two] at this

end DomainTheory.NeighbourhoodSystems.Example13
