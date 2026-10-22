/-ai
The upper bounds of a set of elements are the elements that lie above every member of the set.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise118
public import Mathlib.Tactic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- The family of upper bounds of `X`: `{y ∣ x ⊑ y for all x ∈ X}`. -/
def upperBounds (X : Set V.Element) : Set V.Element := {y | ∀ x ∈ X, x ≤ y}

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
