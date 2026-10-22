module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic.Set
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}


namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


/-- **Proposition 2.6(ii) (Scott 1981, PRG-19).** Composition of approximable mappings becomes
composition of the elementwise functions: `(g ∘ f)(x) = g(f(x))`. Both sides unfold to
`∃ Y X, x.mem X ∧ X f Y ∧ Y g Z`; the proof is a reassociation of existentials. -/
theorem toElementMap_comp (g : ApproximableMap V₁ V₂) (f : ApproximableMap V₀ V₁) (x : V₀.Element) :
    (g.comp f).toElementMap x = g.toElementMap (f.toElementMap x) := by
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨X, hXx, Y, hXY, hYZ⟩
    exact ⟨Y, ⟨X, hXx, hXY⟩, hYZ⟩
  · rintro ⟨Y, ⟨X, hXx, hXY⟩, hYZ⟩
    exact ⟨X, hXx, Y, hXY, hYZ⟩

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
