module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.DomainObj

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
namespace ApproximableMap

open CategoryTheory

/-- Scott's Theorem 2.5: neighbourhood systems and approximable maps form a category —
identity and composition of relations, with the Mathlib unit and associativity laws. -/
theorem theorem_2_5 :
    (∀ {α : Type*} {V : NeighborhoodSystem α} {X Y : Set α},
      (idMap V).rel X Y ↔ V.mem X ∧ V.mem Y ∧ X ⊆ Y) ∧
    (∀ {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {V₂ : NeighborhoodSystem γ} {g : ApproximableMap V₁ V₂} {f : ApproximableMap V₀ V₁}
      {X : Set α} {Z : Set γ},
      (g.comp f).rel X Z ↔ ∃ Y, f.rel X Y ∧ g.rel Y Z) ∧
    (∀ {D E : DomainObj} (f : D ⟶ E), 𝟙 D ≫ f = f) ∧
    (∀ {D E : DomainObj} (f : D ⟶ E), f ≫ 𝟙 E = f) ∧
    (∀ {W X Y Z : DomainObj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),
      (f ≫ g) ≫ h = f ≫ (g ≫ h)) :=
  ⟨@idMap_rel, @comp_rel, Category.id_comp, Category.comp_id, Category.assoc⟩

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
