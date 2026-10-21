/-ai
An element of the final-segment system is total if and only if it equals the limit element.

A total element lies below the limit, and totality applied to the limit, which lies above the element, gives the reverse inequality. Conversely, the limit element is total.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise112.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise112.le_top
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise112.top_isTotal

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise112

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem















/-- `top` is the **unique** total element: an element is total iff it equals `top`. -/
theorem isTotal_iff_top (x : neighborhoodSystem.Element) :
    neighborhoodSystem.IsTotal x ↔ x = top := by
  constructor
  · intro h
    exact le_antisymm (le_top x) (h top (le_top x))
  · rintro rfl; exact top_isTotal

end DomainTheory.NeighbourhoodSystems.Exercise112
