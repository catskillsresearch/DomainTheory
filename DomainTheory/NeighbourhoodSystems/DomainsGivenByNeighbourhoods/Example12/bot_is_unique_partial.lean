/-ai
An element of Example 1.2 that is neither total element is the bottom element.

The classification of elements gives the bottom element or one of the two total elements, and the two total alternatives are excluded by hypothesis.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.element_classification

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example12


namespace neighborhoodSystem

open NeighborhoodSystem


theorem bot_is_unique_partial (x : neighborhoodSystem.Element) :
    x ≠ elemZero → x ≠ elemOne → x = bot := by
  intro hne0 hne1
  rcases element_classification x with hx | hx | hx
  · exact hx
  · exact (hne0 hx).elim
  · exact (hne1 hx).elim

end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example12
