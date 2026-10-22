module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Image
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ : Type*}


namespace ApproximableMap₂

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


/-- **Exercise 2.19 (monotonicity).** The two-variable elementwise map is monotone in each argument
jointly: `x ⊑ x'`, `y ⊑ y'` imply `f(x, y) ⊑ f(x', y')`. -/
theorem toElementMap₂_mono (f : ApproximableMap₂ V₀ V₁ V₂) {x x' : V₀.Element} {y y' : V₁.Element}
    (hx : x ≤ x') (hy : y ≤ y') : f.toElementMap₂ x y ≤ f.toElementMap₂ x' y' := by
  rintro Z ⟨X, Y, hX, hY, hrel⟩
  exact ⟨X, Y, hx X hX, hy Y hY, hrel⟩

end ApproximableMap₂
end DomainTheory.NeighbourhoodSystems
