/-ai
The bottom element of the neighbourhood system of finite nonempty subsets of the natural numbers is the least element of that system.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise114.neighborhoodSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise114.ns_mem

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise114

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- `⊥ = ↑Δ = ↑ℕ`, the least element. -/
def bot : neighborhoodSystem.Element := neighborhoodSystem.bot

end DomainTheory.NeighbourhoodSystems.Exercise114
