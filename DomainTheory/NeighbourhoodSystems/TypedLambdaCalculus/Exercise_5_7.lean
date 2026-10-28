module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_9
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_12
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

@[expose] public section

section

namespace DomainTheory.NeighbourhoodSystems.Exercise507

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ} {V₃ : NeighborhoodSystem δ}

def curry₃ (g : ApproximableMap (prod (prod V₀ V₁) V₂) V₃) :
    ApproximableMap V₀ (funSpace V₁ (funSpace V₂ V₃)) :=
  curry (curry g)

end DomainTheory.NeighbourhoodSystems.Exercise507
end

section
namespace DomainTheory.NeighbourhoodSystems.Exercise507
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

section
variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem app_two_args (σ : ApproximableMap (prod V₀ V₁) V₂) (x : V₀.Element) (y : V₁.Element) :
    σ.toElementMap (pair x y) =
      (toApproxMap ((curry σ).toElementMap x)).toElementMap y := by
  rw [toElementMap_curry_apply]

theorem curry₃_apply (g : ApproximableMap (prod (prod V₀ V₁) V₂) V₃)
    (x : V₀.Element) (y : V₁.Element) (z : V₂.Element) :
    (toApproxMap ((toApproxMap ((curry₃ g).toElementMap x)).toElementMap y)).toElementMap z =
      g.toElementMap (pair (pair x y) z) := by
  rw [curry₃, toElementMap_curry_apply, toElementMap_curry_apply]

theorem lam_two_vars (g : ApproximableMap (prod V₀ V₁) V₂) (x : V₀.Element) (y : V₁.Element) :
    (toApproxMap ((curry g).toElementMap x)).toElementMap y = g.toElementMap (pair x y) :=
  toElementMap_curry_apply g x y

theorem surjective_pairing (z : (prod V₀ V₁).Element) :
    pair ((proj₀ V₀ V₁).toElementMap z) ((proj₁ V₀ V₁).toElementMap z) = z := by
  rw [toElementMap_proj₀, toElementMap_proj₁, pair_fst_snd]

theorem uncurry_apply (h : ApproximableMap V₀ (funSpace V₁ V₂))
    (x : V₀.Element) (y : V₁.Element) :
    (uncurry h).toElementMap (pair x y) =
      (toApproxMap (h.toElementMap x)).toElementMap y := by
  rw [uncurry_eq, toElementMap_comp, toElementMap_paired, toElementMap_comp,
    toElementMap_proj₀, toElementMap_proj₁, fst_pair, snd_pair, evalMap_apply]

theorem uncurry_lam_two_vars (g : ApproximableMap (prod V₀ V₁) V₂) : uncurry (curry g) = g :=
  uncurry_curry g

end

end DomainTheory.NeighbourhoodSystems.Exercise507
end
