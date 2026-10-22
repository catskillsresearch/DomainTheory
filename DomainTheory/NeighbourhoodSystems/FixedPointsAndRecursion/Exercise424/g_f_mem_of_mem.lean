module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise424.sbSet
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise424.sbSet_isFixed

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise424

open DomainTheory.NeighbourhoodSystems.Exercise414 Function

variable {A B : Type*} {f : A → B} {g : B → A}

/-- `g(f(a)) ∈ X` whenever `a ∈ X` (the `g(f(X)) ⊆ T(X) = X` half). -/
theorem g_f_mem_of_mem {a : A} (ha : a ∈ sbSet f g) : g (f a) ∈ sbSet f g := by
  rw [← sbSet_isFixed]
  exact Or.inr ⟨f a, ⟨a, ha, rfl⟩, rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise424
