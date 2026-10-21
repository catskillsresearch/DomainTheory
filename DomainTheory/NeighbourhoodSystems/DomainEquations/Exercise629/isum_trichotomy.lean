/-ai
Every element of the indexed separated sum either contains the tagged copy of some neighbourhood or contains only the master.

Split on whether such a tagged copy exists. If it does, that is the first alternative. If it does not, any neighbourhood of the element is either the master or a tagged copy of a neighbourhood, and the second case is excluded by the case hypothesis.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Basic
import all Mathlib.Data.Finset.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}


variable {D : ∀ i, NeighborhoodSystem (α i)}


/-- **Exercise 6.29 — sum trichotomy.** Every element of `∑_i D_i` either reaches into some summand
or is the basepoint `⊥`. (Prop-level and genuinely classical: the case split is excluded middle on
whether `z` reaches a summand, so this depends on `Classical.choice`.) -/
theorem isum_trichotomy {hne : ∀ i, ∀ X : Set (α i), (D i).mem X → X.Nonempty}
    (z : (isum D hne).Element) :
    (∃ i, ∃ X : Set (α i), (D i).mem X ∧ z.mem (injI i X)) ∨
      (∀ W, z.mem W → W = (isum D hne).master) := by
  by_cases h : ∃ i, ∃ X : Set (α i), (D i).mem X ∧ z.mem (injI i X)
  · exact Or.inl h
  · refine Or.inr fun W hW => ?_
    rcases z.sub hW with rfl | ⟨i, X, hX, rfl⟩
    · rfl
    · exact absurd ⟨i, X, hX, hW⟩ h

end Exercise629
end DomainTheory.NeighbourhoodSystems
