/-ai
The up-set of a set is the set of neighbourhoods contained in it.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- Exercise 1.20's `↑X = {Y ∈ 𝒟 ∣ Y ⊆ X}` (the up-set of `X` *inside* `𝒟`). -/
def upSet (X : Set α) : Set (Set α) := {Y | V.mem Y ∧ Y ⊆ X}

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
