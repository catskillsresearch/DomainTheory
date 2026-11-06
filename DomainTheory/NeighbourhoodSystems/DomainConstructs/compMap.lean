module
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_12
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6
@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap
section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

def compApp (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (prod (prod (funSpace V₁ V₂) (funSpace V₀ V₁)) V₀) V₂ :=
  (evalMap V₁ V₂).comp
    (paired
      ((proj₀ (funSpace V₁ V₂) (funSpace V₀ V₁)).comp
        (proj₀ (prod (funSpace V₁ V₂) (funSpace V₀ V₁)) V₀))
      ((evalMap V₀ V₁).comp
        (paired
          ((proj₁ (funSpace V₁ V₂) (funSpace V₀ V₁)).comp
            (proj₀ (prod (funSpace V₁ V₂) (funSpace V₀ V₁)) V₀))
          (proj₁ (prod (funSpace V₁ V₂) (funSpace V₀ V₁)) V₀))))

def compMap (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (prod (funSpace V₁ V₂) (funSpace V₀ V₁)) (funSpace V₀ V₂) :=
  curry (compApp V₀ V₁ V₂)

theorem toElementMap_compApp (Gφ : (funSpace V₁ V₂).Element) (Fφ : (funSpace V₀ V₁).Element)
    (x : V₀.Element) :
    (compApp V₀ V₁ V₂).toElementMap (pair (pair Gφ Fφ) x)
      = (toApproxMap Gφ).toElementMap ((toApproxMap Fφ).toElementMap x) := by
  rw [compApp]
  simp only [toElementMap_comp, toElementMap_paired, toElementMap_proj₀, toElementMap_proj₁,
    fst_pair, snd_pair, evalMap_apply]

theorem toElementMap_compMap_apply (Gφ : (funSpace V₁ V₂).Element) (Fφ : (funSpace V₀ V₁).Element)
    (x : V₀.Element) :
    (toApproxMap ((compMap V₀ V₁ V₂).toElementMap (pair Gφ Fφ))).toElementMap x
      = (toApproxMap Gφ).toElementMap ((toApproxMap Fφ).toElementMap x) := by
  rw [compMap, toElementMap_curry_apply, toElementMap_compApp]

theorem toApproxMap_compMap (Gφ : (funSpace V₁ V₂).Element) (Fφ : (funSpace V₀ V₁).Element) :
    toApproxMap ((compMap V₀ V₁ V₂).toElementMap (pair Gφ Fφ))
      = (toApproxMap Gφ).comp (toApproxMap Fφ) := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_compMap_apply, toElementMap_comp]
end

end
end DomainTheory.NeighbourhoodSystems
end
