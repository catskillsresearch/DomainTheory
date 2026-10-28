module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_12
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Definition_3_3
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Lemma_3_6

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

section
variable {α β γ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

theorem theorem_51 :
    (∀ (g : ApproximableMap (prod V₀ V₁) V₂) (v : V₀.Element) (x : V₁.Element),
      (toApproxMap ((curry g).toElementMap v)).toElementMap x = g.toElementMap (pair v x)) ∧
    (∀ (F : ApproximableMap V₂ (funSpace V₀ V₁)) (G : ApproximableMap V₂ V₀) (w : V₂.Element),
      ((evalMap V₀ V₁).comp (paired F G)).toElementMap w =
        (toApproxMap (F.toElementMap w)).toElementMap (G.toElementMap w)) ∧
    (∀ (k : V₁.Element) (x : V₀.Element), (constMap V₀ k).toElementMap x = k) ∧
    (∀ (f : ApproximableMap V₂ V₀) (g : ApproximableMap V₂ V₁) (w : V₂.Element),
      (paired f g).toElementMap w = pair (f.toElementMap w) (g.toElementMap w)) ∧
    (∀ (x : V₀.Element) (y : V₁.Element), (proj₀ V₀ V₁).toElementMap (pair x y) = x) :=
  ⟨fun g v x => toElementMap_curry_apply g v x,
   fun F G w => toElementMap_evalMap_comp_paired F G w,
   fun k x => toElementMap_constMap k x,
   fun f g w => toElementMap_paired f g w,
   fun x y => toElementMap_proj₀_pair x y⟩

end
end DomainTheory.NeighbourhoodSystems
