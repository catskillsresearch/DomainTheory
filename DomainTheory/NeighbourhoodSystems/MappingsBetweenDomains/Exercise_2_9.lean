module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_2
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem

section
variable {α β γ : Type*}

namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

theorem toElementMap_mem_iff_principal (f : ApproximableMap V₀ V₁) (x : V₀.Element) {Y : Set β} :
    (f.toElementMap x).mem Y ↔
      ∃ (X : Set α) (hx : x.mem X), (f.toElementMap (V₀.principal (x.sub hx))).mem Y := by
  rw [mem_toElementMap]
  constructor
  · rintro ⟨X, hxX, hrel⟩
    exact ⟨X, hxX, (f.rel_iff_mem_principal (x.sub hxX)).mp hrel⟩
  · rintro ⟨X, hxX, hmem⟩
    exact ⟨X, hxX, (f.rel_iff_mem_principal (x.sub hxX)).mpr hmem⟩

end ApproximableMap
end

end DomainTheory.NeighbourhoodSystems
