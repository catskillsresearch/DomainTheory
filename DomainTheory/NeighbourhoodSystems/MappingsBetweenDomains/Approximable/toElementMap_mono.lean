module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic.Set
import all Mathlib.Tactic.Set
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}



namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}




/-- **Proposition 2.2(iii) (Scott 1981, PRG-19).** Approximable maps are monotone on elements:
`x ⊑ y ⟹ f(x) ⊑ f(y)`. -/
theorem toElementMap_mono (f : ApproximableMap V₀ V₁) {x y : V₀.Element} (hxy : x ≤ y) :
    f.toElementMap x ≤ f.toElementMap y := by
  rintro Y ⟨X, hX, hXY⟩
  exact ⟨X, hxy X hX, hXY⟩

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
