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


/-- **Exercise 2.12.** The induced elementwise map is the pointwise union: `g(x) = ⋃ᵢ f i (x)`. -/
theorem mem_toElementMap_iSupMap {I : Type*} [Nonempty I] (f : I → ApproximableMap V₀ V₁)
    (hdir : ∀ i j, ∃ k, (∀ X Y, (f i).rel X Y → (f k).rel X Y) ∧
      (∀ X Y, (f j).rel X Y → (f k).rel X Y)) (x : V₀.Element) {Y : Set β} :
    ((iSupMap f hdir).toElementMap x).mem Y ↔ ∃ i, ((f i).toElementMap x).mem Y := by
  constructor
  · rintro ⟨X, hxX, i, hrel⟩
    exact ⟨i, X, hxX, hrel⟩
  · rintro ⟨i, X, hxX, hrel⟩
    exact ⟨X, hxX, i, hrel⟩

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
