/-ai
An element of a neighbourhood system is a filter of neighbourhoods: a family contained in the system, containing the master, closed under binary intersection, and upward closed within the system. This is Scott's Definition 1.6.
ai-/
module


public import Mathlib.Data.Set.Basic
public import Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.NeighborhoodSystem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Definition 1.6 (Scott 1981, PRG-19).** An (ideal) *element* of a neighbourhood system:
a subfamily `x ⊆ 𝒟` that is a *filter* — (i) `Δ ∈ x`, (ii) closed under intersection, (iii)
upward closed within `𝒟`. The domain is the type `Element` of all such filters, ordered by
inclusion. -/
structure Element where
  /-- `mem X` holds iff the neighbourhood `X` belongs to the filter `x`. -/
  mem : Set α → Prop
  /-- `x` is a subfamily of `𝒟`. -/
  sub : ∀ {X}, mem X → V.mem X
  /-- (i) `Δ ∈ x`. -/
  master_mem : mem V.master
  /-- (ii) `X, Y ∈ x ⟹ X ∩ Y ∈ x`. -/
  inter_mem : ∀ {X Y}, mem X → mem Y → mem (X ∩ Y)
  /-- (iii) `X ∈ x` and `X ⊆ Y ∈ 𝒟 ⟹ Y ∈ x`. -/
  up_mem : ∀ {X Y}, mem X → V.mem Y → X ⊆ Y → mem Y

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
