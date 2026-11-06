module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.stepEq

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

/-- Scott's Exercise 3.21: criterion for identity of step neighbourhoods. -/
theorem example_321 :
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {Y : Set α} {Z : Set β} (_hY : V₀.mem Y) (_hZ : V₁.mem Z)
      {Y' : Set α} {Z' : Set β} (_hY' : V₀.mem Y') (_hZ' : V₁.mem Z'),
      (step Y Z : Set (ApproximableMap V₀ V₁)) = step Y' Z' ↔
        (Z = V₁.master ∧ Z' = V₁.master) ∨ (Y = Y' ∧ Z = Z')) ∧
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {Y : Set α} {Z : Set β} (_hY : V₀.mem Y) (_hZ : V₁.mem Z)
      {Y' : Set α} {Z' : Set β} (_hY' : V₀.mem Y') (_hZ' : V₁.mem Z'),
      Z ≠ V₁.master →
        (step Y Z : Set (ApproximableMap V₀ V₁)) = step Y' Z' → Y = Y' ∧ Z = Z') ∧
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      (Y : Set α) (_hY : V₀.mem Y),
      (step Y V₁.master : Set (ApproximableMap V₀ V₁)) = Set.univ) :=
  ⟨@step_eq_iff, @step_eq_of_ne_master, @step_master_right⟩

end DomainTheory.NeighbourhoodSystems
