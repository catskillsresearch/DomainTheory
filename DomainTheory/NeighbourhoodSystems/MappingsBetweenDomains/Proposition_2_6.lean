module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.idMap

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
namespace ApproximableMap

/-- Scott's Proposition 2.6: the identity acts as the identity on elements, and composition
of approximable maps acts by composition of the elementwise maps. -/
theorem proposition_2_6 :
    (∀ {α : Type*} {V : NeighborhoodSystem α} (x : V.Element),
      (idMap V).toElementMap x = x) ∧
    (∀ {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {V₂ : NeighborhoodSystem γ} (g : ApproximableMap V₁ V₂) (f : ApproximableMap V₀ V₁)
      (x : V₀.Element),
      (g.comp f).toElementMap x = g.toElementMap (f.toElementMap x)) :=
  ⟨@toElementMap_idMap, @toElementMap_comp⟩

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
