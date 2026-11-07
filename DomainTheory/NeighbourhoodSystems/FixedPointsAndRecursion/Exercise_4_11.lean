module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.fixUniform

@[expose] public section

open DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

theorem example_411 :
    ∀ (F : ∀ {β : Type u} (W : NeighborhoodSystem β), ApproximableMap W W → W.Element),
      (∀ {β : Type u} (W : NeighborhoodSystem β) (g : ApproximableMap W W),
        g.toElementMap (F W g) = F W g) →
      (∀ {β γ : Type u} (W₀ : NeighborhoodSystem β) (W₁ : NeighborhoodSystem γ)
        (g₀ : ApproximableMap W₀ W₀) (g₁ : ApproximableMap W₁ W₁) (h : ApproximableMap W₀ W₁),
        h.toElementMap W₀.bot = W₁.bot →
        (∀ x, h.toElementMap (g₀.toElementMap x) = g₁.toElementMap (h.toElementMap x)) →
        h.toElementMap (F W₀ g₀) = F W₁ g₁) →
      ∀ {α : Type u} (V : NeighborhoodSystem α) (f : ApproximableMap V V),
        F V f = f.fixElement :=
  fun F hfixed huniform => fix_unique_of_uniform F hfixed huniform

