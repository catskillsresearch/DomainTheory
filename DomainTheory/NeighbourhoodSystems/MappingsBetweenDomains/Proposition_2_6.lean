module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Theorem_2_5
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem

section
variable {α β γ δ : Type*}

namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

theorem toElementMap_comp (g : ApproximableMap V₁ V₂) (f : ApproximableMap V₀ V₁) (x : V₀.Element) :
    (g.comp f).toElementMap x = g.toElementMap (f.toElementMap x) := by
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨X, hXx, Y, hXY, hYZ⟩
    exact ⟨Y, ⟨X, hXx, hXY⟩, hYZ⟩
  · rintro ⟨Y, ⟨X, hXx, hXY⟩, hYZ⟩
    exact ⟨X, hXx, Y, hXY, hYZ⟩

theorem commute_apply {V : NeighborhoodSystem α} {f g : ApproximableMap V V}
    (hcomm : f.comp g = g.comp f) (x : V.Element) :
    f.toElementMap (g.toElementMap x) = g.toElementMap (f.toElementMap x) := by
  have h1 : (f.comp g).toElementMap x = (g.comp f).toElementMap x := by rw [hcomm]
  rwa [toElementMap_comp, toElementMap_comp] at h1

end ApproximableMap
end

end DomainTheory.NeighbourhoodSystems
