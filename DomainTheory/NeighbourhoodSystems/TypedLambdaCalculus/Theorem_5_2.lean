module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_9
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_12
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Lemma_3_6

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap
section
variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
namespace Theorem52

theorem beta (g : ApproximableMap (prod V₀ V₁) V₂) (σ : V₁.Element) :
    (evalMap V₁ V₂).comp (paired (curry g) (constMap V₀ σ))
      = g.comp (paired (idMap V₀) (constMap V₀ σ)) := by
  apply ext_of_toElementMap
  intro v
  rw [toElementMap_comp, toElementMap_paired, evalMap_apply, toElementMap_curry_apply,
    toElementMap_constMap, toElementMap_comp, toElementMap_paired, toElementMap_idMap,
    toElementMap_constMap]

theorem beta_abs (g : ApproximableMap (prod (prod V₀ V₁) V₂) V₃) (v : V₀.Element) (σ : V₁.Element)
    (y : V₂.Element) :
    (toApproxMap ((toApproxMap ((curry (curry g)).toElementMap v)).toElementMap σ)).toElementMap y
      = g.toElementMap (pair (pair v σ) y) := by
  rw [toElementMap_curry_apply, toElementMap_curry_apply]

theorem beta_tuple (g₀ : ApproximableMap (prod V₀ V₁) V₂) (g₁ : ApproximableMap (prod V₀ V₁) V₃)
    (v : V₀.Element) (x : V₁.Element) :
    (toApproxMap ((curry (paired g₀ g₁)).toElementMap v)).toElementMap x
      = pair ((toApproxMap ((curry g₀).toElementMap v)).toElementMap x)
          ((toApproxMap ((curry g₁).toElementMap v)).toElementMap x) := by
  rw [toElementMap_curry_apply, toElementMap_paired, toElementMap_curry_apply,
    toElementMap_curry_apply]

theorem subst_value (g : ApproximableMap (prod V₀ V₁) V₂) (v : V₀.Element) (x : V₁.Element) :
    (toApproxMap ((curry g).toElementMap v)).toElementMap x = g.toElementMap (pair v x) :=
  toElementMap_curry_apply g v x

end Theorem52
end

end DomainTheory.NeighbourhoodSystems
end
