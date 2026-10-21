/-ai
A neighbourhood belongs to an indexed directed union if and only if it belongs to some member of the family.

Membership in the underlying directed union is membership in some value of the family. In the other direction that value is a member of the range.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Image
import all Mathlib.Data.Set.Image
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ : Type*}

namespace NeighborhoodSystem


theorem mem_iSupDirected {α : Type*} {V : NeighborhoodSystem α} {I : Type*} [Nonempty I]
    (a : I → V.Element) (hdir : ∀ i j, ∃ k, a i ≤ a k ∧ a j ≤ a k) {Z : Set α} :
    (iSupDirected a hdir).mem Z ↔ ∃ i, (a i).mem Z := by
  constructor
  · rintro ⟨s, ⟨i, rfl⟩, hsZ⟩; exact ⟨i, hsZ⟩
  · rintro ⟨i, hi⟩; exact ⟨a i, ⟨i, rfl⟩, hi⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
