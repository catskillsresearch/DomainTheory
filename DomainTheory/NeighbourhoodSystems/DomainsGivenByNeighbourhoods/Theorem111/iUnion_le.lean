/-ai
If an element lies above every term of an ascending sequence, it lies above the union of the sequence.

A set belonging to the union belongs to some term, and that term lies below the element.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Order.Monotone.Basic
import all Mathlib.Order.Monotone.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem111.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)







/-- `⋃ₙ xₙ` is the **least** upper bound: anything approximated by all `xₙ` approximates the
union from above. -/
theorem iUnion_le (x : ℕ → V.Element) (hmono : Monotone x) (y : V.Element)
    (h : ∀ n, x n ≤ y) : V.iUnion x hmono ≤ y := by
  rintro X ⟨n, hn⟩
  exact h n X hn

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
