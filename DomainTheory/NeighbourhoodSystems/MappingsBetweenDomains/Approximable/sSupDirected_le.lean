/-ai
The directed union of a nonempty directed family lies below any element that lies above every member of the family.

A neighbourhood of the union belongs to some member, and that member lies below the upper bound.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic.Set
import all Mathlib.Tactic.Set
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

namespace NeighborhoodSystem


/-- The directed union is the least upper bound: an upper bound of every member dominates it. -/
theorem sSupDirected_le (V : NeighborhoodSystem α) (S : Set V.Element) (hne : S.Nonempty)
    (hdir : ∀ a ∈ S, ∀ b ∈ S, ∃ c ∈ S, a ≤ c ∧ b ≤ c) {y : V.Element}
    (hy : ∀ s ∈ S, s ≤ y) : V.sSupDirected S hne hdir ≤ y := by
  rintro Z ⟨s, hs, hsZ⟩
  exact hy s hs Z hsZ

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
