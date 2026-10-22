module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-- The embedding `T × D₀ × D₁ → T × S × S` (`S = D₀ + D₁`) that injects the two value slots into
the sum via `in₀` and `in₁`, leaving the truth slot fixed. -/
def condSumEmb (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty) :
    ApproximableMap (prod TD (prod V₀ V₁)) (prod TD (prod (sum V₀ V₁ h₀ h₁) (sum V₀ V₁ h₀ h₁))) :=
  paired (proj₀ TD (prod V₀ V₁))
    (paired ((inMap₀ (h₀ := h₀) (h₁ := h₁)).comp ((proj₀ V₀ V₁).comp (proj₁ TD (prod V₀ V₁))))
      ((inMap₁ (h₀ := h₀) (h₁ := h₁)).comp ((proj₁ V₀ V₁).comp (proj₁ TD (prod V₀ V₁)))))

end DomainTheory.NeighbourhoodSystems.Exercise326
