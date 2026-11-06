module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.sumSys

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

/-- Scott's Exercise 3.18: injections into a separated sum have left inverses. -/
theorem example_318 :
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty},
      (outMap₀ (V₀ := V₀) (V₁ := V₁) (h₀ := h₀) (h₁ := h₁)).comp inMap₀ = idMap V₀) ∧
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty},
      (outMap₁ (V₀ := V₀) (V₁ := V₁) (h₀ := h₀) (h₁ := h₁)).comp inMap₁ = idMap V₁) :=
  ⟨@outMap₀_comp_inMap₀, @outMap₁_comp_inMap₁⟩

end DomainTheory.NeighbourhoodSystems
