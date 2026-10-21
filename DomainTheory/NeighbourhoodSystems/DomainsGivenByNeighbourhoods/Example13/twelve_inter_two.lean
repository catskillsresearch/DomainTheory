/-ai
The intersection of {1, 2} and {2} equals {2}.

Extensionality reduces the equality to membership of a token. Case analysis on the three tokens, together with the two neighbourhood definitions, settles each case.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.twelve
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.two

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example13

theorem twelve_inter_two : twelve ∩ two = two := by
  ext t
  fin_cases t <;> simp [twelve, two]

end DomainTheory.NeighbourhoodSystems.Example13
