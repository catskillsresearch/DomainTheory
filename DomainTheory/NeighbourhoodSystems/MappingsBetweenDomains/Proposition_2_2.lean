module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableMap
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
namespace ApproximableMap

/-- Scott's Proposition 2.2: approximable maps act elementwise; the action recovers the
relation on principals; it is monotone; and equal actions determine equal relations. -/
theorem proposition_2_2 :
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      (f : ApproximableMap V₀ V₁) (x : V₀.Element) {Y : Set β},
      (f.toElementMap x).mem Y ↔ ∃ X, x.mem X ∧ f.rel X Y) ∧
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      (f : ApproximableMap V₀ V₁) {X : Set α} (hX : V₀.mem X) {Y : Set β},
      f.rel X Y ↔ (f.toElementMap (V₀.principal hX)).mem Y) ∧
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      (f : ApproximableMap V₀ V₁) {x y : V₀.Element},
      x ≤ y → f.toElementMap x ≤ f.toElementMap y) ∧
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {f g : ApproximableMap V₀ V₁},
      (∀ x, f.toElementMap x = g.toElementMap x) → f = g) :=
  ⟨mem_toElementMap, rel_iff_mem_principal, toElementMap_mono, ext_of_toElementMap⟩

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
