module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Image
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ : Type*}


namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


/-- **Exercise 2.9 (Scott 1981, PRG-19).** `f(x) = ⋃ {f(↑X) ∣ X ∈ x}`: a neighbourhood `Y` lies in
`f(x)` iff it lies in `f(↑X)` for some `X ∈ x`. (Immediate from `rel_iff_mem_principal`.) -/
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
end DomainTheory.NeighbourhoodSystems
