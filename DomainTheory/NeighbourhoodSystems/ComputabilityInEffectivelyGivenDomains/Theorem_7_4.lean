module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.sumEffective
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.prodEffective

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive ApproximableMap IndefProduct

/-- Scott's Theorem 7.4: effective givenness and computability for sum and product. -/
theorem theorem_74 :
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty},
      V₀.IsEffectivelyGiven → V₁.IsEffectivelyGiven → (sum V₀ V₁ h₀ h₁).IsEffectivelyGiven) ∧
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
      (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁),
      ComputableMap P₀ (sumPresentation P₀ P₁ (h₀ := h₀) (h₁ := h₁))
        (inMap₀ (h₀ := h₀) (h₁ := h₁))) ∧
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
      (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁),
      ComputableMap P₁ (sumPresentation P₀ P₁ (h₀ := h₀) (h₁ := h₁))
        (inMap₁ (h₀ := h₀) (h₁ := h₁))) ∧
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
      (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁),
      ComputableMap (sumPresentation P₀ P₁ (h₀ := h₀) (h₁ := h₁)) P₀
        (outMap₀ (h₀ := h₀) (h₁ := h₁))) ∧
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
      (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁),
      ComputableMap (sumPresentation P₀ P₁ (h₀ := h₀) (h₁ := h₁)) P₁
        (outMap₁ (h₀ := h₀) (h₁ := h₁))) ∧
    (∀ {α β α' β' : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
      {P₀ : ComputablePresentation V₀} {P₁ : ComputablePresentation V₁}
      {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}
      {h₀' : ∀ X, V₀'.mem X → X.Nonempty} {h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty}
      (Q₀ : ComputablePresentation V₀') (Q₁ : ComputablePresentation V₁')
      {f : ApproximableMap V₀ V₀'} {g : ApproximableMap V₁ V₁'},
      ComputableMap P₀ Q₀ f → ComputableMap P₁ Q₁ g →
        ComputableMap (sumPresentation P₀ P₁ (h₀ := h₀) (h₁ := h₁))
          (sumPresentation Q₀ Q₁ (h₀ := h₀') (h₁ := h₁'))
          (sumMap (h₀ := h₀) (h₁ := h₁) (h₀' := h₀') (h₁' := h₁') f g)) ∧
    (∀ {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {V₂ : NeighborhoodSystem γ} {P₂ : ComputablePresentation V₂}
      {P₀ : ComputablePresentation V₀} {P₁ : ComputablePresentation V₁}
      {a : ApproximableMap V₂ V₀} {b : ApproximableMap V₂ V₁},
      ComputableMap P₂ P₀ a → ComputableMap P₂ P₁ b →
        ComputableMap P₂ (prodPresentation P₀ P₁) (paired a b)) ∧
    (∀ {α β α' β' : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}
      {P₀ : ComputablePresentation V₀} {P₁ : ComputablePresentation V₁}
      {P₀' : ComputablePresentation V₀'} {P₁' : ComputablePresentation V₁'}
      {f : ApproximableMap V₀ V₀'} {g : ApproximableMap V₁ V₁'},
      ComputableMap P₀ P₀' f → ComputableMap P₁ P₁' g →
        ComputableMap (prodPresentation P₀ P₁) (prodPresentation P₀' P₁') (prodMap f g)) ∧
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β},
      V₀.IsEffectivelyGiven → V₁.IsEffectivelyGiven → (prod V₀ V₁).IsEffectivelyGiven) ∧
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁),
      ComputableMap (prodPresentation P₀ P₁) P₀ (proj₀ V₀ V₁)) ∧
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁),
      ComputableMap (prodPresentation P₀ P₁) P₁ (proj₁ V₀ V₁)) :=
  ⟨@sum_isEffectivelyGiven, ⟨@inMap₀_isComputable, ⟨@inMap₁_isComputable,
    ⟨@outMap₀_isComputable, ⟨@outMap₁_isComputable, ⟨@sumMap_isComputable,
      ⟨@paired_isComputable, ⟨@prodMap_isComputable, ⟨@prod_isEffectivelyGiven,
        ⟨@proj₀_isComputable, @proj₁_isComputable⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end DomainTheory.NeighbourhoodSystems
