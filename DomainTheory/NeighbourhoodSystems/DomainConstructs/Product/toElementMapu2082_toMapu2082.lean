module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}










variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}





















variable {V₂ : NeighborhoodSystem γ}

open ApproximableMap






















/-- **Theorem 3.5 (elementwise) (Scott 1981, PRG-19).** The two-variable elementwise map of
`toMap₂ f` is `f` evaluated at the pairing: `(toMap₂ f)(x, y) = f(⟨x, y⟩)`. -/
theorem toElementMap₂_toMap₂ (f : ApproximableMap (prod V₀ V₁) V₂) (x : V₀.Element) (y : V₁.Element) :
    (toMap₂ f).toElementMap₂ x y = f.toElementMap (pair x y) := by
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨X, Y, hX, hY, hrel⟩
    exact ⟨prodNbhd X Y, ⟨X, Y, hX, hY, rfl⟩, hrel⟩
  · rintro ⟨W, ⟨X, Y, hX, hY, rfl⟩, hrel⟩
    exact ⟨X, Y, hX, hY, hrel⟩

end DomainTheory.NeighbourhoodSystems
