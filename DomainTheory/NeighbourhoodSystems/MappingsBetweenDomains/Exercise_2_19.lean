module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableMap2

@[expose] public section

open DomainTheory.NeighbourhoodSystems
open ApproximableMap₂


/-- Scott's Exercise 2.19: the elementwise action of a binary approximable map recovers the
ternary neighbourhood relation on principals and is monotone in each argument. -/
theorem exercise_2_19 :
    (∀ {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {V₂ : NeighborhoodSystem γ} (f : ApproximableMap₂ V₀ V₁ V₂)
      (x : V₀.Element) (y : V₁.Element) {Z : Set γ},
      (f.toElementMap₂ x y).mem Z ↔ ∃ X Y, x.mem X ∧ y.mem Y ∧ f.rel X Y Z) ∧
    (∀ {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {V₂ : NeighborhoodSystem γ} (f : ApproximableMap₂ V₀ V₁ V₂)
      {X : Set α} (hX : V₀.mem X) {Y : Set β} (hY : V₁.mem Y) {Z : Set γ},
      f.rel X Y Z ↔ (f.toElementMap₂ (V₀.principal hX) (V₁.principal hY)).mem Z) ∧
    (∀ {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {V₂ : NeighborhoodSystem γ} (f : ApproximableMap₂ V₀ V₁ V₂)
      {x x' : V₀.Element} {y y' : V₁.Element},
      x ≤ x' → y ≤ y' → f.toElementMap₂ x y ≤ f.toElementMap₂ x' y') :=
  ⟨@ApproximableMap₂.mem_toElementMap₂, @ApproximableMap₂.rel₂_iff_mem_principal,
    @ApproximableMap₂.toElementMap₂_mono⟩

