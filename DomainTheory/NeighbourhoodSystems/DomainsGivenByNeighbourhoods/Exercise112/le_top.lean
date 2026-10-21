/-ai
Every element of the final-segment system approximates the limit element.

A neighbourhood of the element is a neighbourhood of the system, which is membership in the limit.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise112.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise112

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem















/-- `top` is the greatest element of `|𝒟|`: every element approximates it. -/
theorem le_top (x : neighborhoodSystem.Element) : x ≤ top :=
  fun _ hX => x.sub hX

end DomainTheory.NeighbourhoodSystems.Exercise112
