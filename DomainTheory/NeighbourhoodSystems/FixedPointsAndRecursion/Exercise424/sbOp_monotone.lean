/-ai
Tarski's operator is monotone.

An element of the complement of the range remains there. An element of the image of the smaller set comes from an element of that set, which lies in the larger set by the assumed inclusion.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise424.sbOp

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise424

open DomainTheory.NeighbourhoodSystems.Exercise414 Function

variable {A B : Type*} {f : A → B} {g : B → A}

theorem sbOp_monotone (f : A → B) (g : B → A) : Monotone (sbOp f g) := by
  intro X Y hXY a ha
  rcases ha with ha | ⟨b, ⟨x, hx, rfl⟩, rfl⟩
  · exact Or.inl ha
  · exact Or.inr ⟨f x, ⟨x, hXY hx, rfl⟩, rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise424
