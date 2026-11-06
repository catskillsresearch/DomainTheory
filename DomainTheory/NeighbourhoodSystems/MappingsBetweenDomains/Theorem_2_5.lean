module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.idMap

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
namespace ApproximableMap

/-- Scott's Theorem 2.5: neighbourhood systems and approximable maps form a category —
identity and composition of relations, with the usual unit and associativity laws. -/
theorem theorem_2_5 :
    (∀ {α : Type*} {V : NeighborhoodSystem α} {X Y : Set α},
      (idMap V).rel X Y ↔ V.mem X ∧ V.mem Y ∧ X ⊆ Y) ∧
    (∀ {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {V₂ : NeighborhoodSystem γ} {g : ApproximableMap V₁ V₂} {f : ApproximableMap V₀ V₁}
      {X : Set α} {Z : Set γ},
      (g.comp f).rel X Z ↔ ∃ Y, f.rel X Y ∧ g.rel Y Z) ∧
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      (f : ApproximableMap V₀ V₁), f.comp (idMap V₀) = f) ∧
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      (f : ApproximableMap V₀ V₁), (idMap V₁).comp f = f) ∧
    (∀ {α β γ δ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {V₂ : NeighborhoodSystem γ} {V₃ : NeighborhoodSystem δ}
      (h : ApproximableMap V₂ V₃) (g : ApproximableMap V₁ V₂) (f : ApproximableMap V₀ V₁),
      (h.comp g).comp f = h.comp (g.comp f)) :=
  ⟨@idMap_rel, @comp_rel, @comp_idMap, @idMap_comp, @comp_assoc⟩

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
