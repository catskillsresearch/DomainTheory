module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.cond

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise326
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap Truth

/-- Scott's Exercise 3.26: conditional at true, false, and bottom. -/
theorem example_326 :
    (∀ {α : Type*} (V : NeighborhoodSystem α) (x y : V.Element),
      (cond V).toElementMap (pair trueElt (pair x y)) = x) ∧
    (∀ {α : Type*} (V : NeighborhoodSystem α) (x y : V.Element),
      (cond V).toElementMap (pair falseElt (pair x y)) = y) ∧
    (∀ {α : Type*} (V : NeighborhoodSystem α) (x y : V.Element),
      (cond V).toElementMap (pair botElt (pair x y)) = V.bot) :=
  ⟨@cond_true, @cond_false, @cond_bot⟩

/-- Scott's Exercise 3.26: sum-valued conditional and recovery via which. -/
theorem example_326_sum :
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
      (x : V₀.Element) (y : V₁.Element),
      (condSum V₀ V₁ h₀ h₁).toElementMap (pair botElt (pair x y)) = (sum V₀ V₁ h₀ h₁).bot) ∧
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
      (x : V₀.Element) (y : V₁.Element),
      (condSum V₀ V₁ h₀ h₁).toElementMap (pair falseElt (pair x y))
        = (inMap₁ (h₀ := h₀) (h₁ := h₁)).toElementMap y) ∧
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
      (x : V₀.Element) (y : V₁.Element),
      (condSum V₀ V₁ h₀ h₁).toElementMap (pair trueElt (pair x y))
        = (inMap₀ (h₀ := h₀) (h₁ := h₁)).toElementMap x) ∧
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
      (x : (sum V₀ V₁ h₀ h₁).Element),
      (cond (sum V₀ V₁ h₀ h₁)).toElementMap
          (pair ((whichMap V₀ V₁ h₀ h₁).toElementMap x)
            (pair ((inMap₀ (h₀ := h₀) (h₁ := h₁)).toElementMap
                    ((outMap₀ (h₀ := h₀) (h₁ := h₁)).toElementMap x))
                  ((inMap₁ (h₀ := h₀) (h₁ := h₁)).toElementMap
                    ((outMap₁ (h₀ := h₀) (h₁ := h₁)).toElementMap x)))) = x) :=
  ⟨@condSum_bot, @condSum_false, @condSum_true, @cond_which⟩

end DomainTheory.NeighbourhoodSystems.Exercise326
